//! Value types for arbitrary parsing of Marshal structures.

use core::fmt::Debug;

use ruby_marshal_derive::FromRubyMarshal;

use crate::de::{FromRubyMarshal, ParsingError, RubyRegexp, RubyType, RubyTypeTag};

/// Represents any valid Ruby Marshal value (low-level).
///
/// Using this type as the target when trying to deserialize should always work
/// (as long as the data is not malformed) and will produce a tree of Ruby Marshal
/// values roughly corresponding to that of the original data (with symlinks and
/// object links resolved).
///
/// `ValueLL` tries to be as "pedal-to-the-metal" as possible; in particular,
/// it does not attempt to do any preprocessing beyond resolution of symlinks
/// and object links. This implies that strings and regular expressions will be
/// found in their IVAR forms.
///
/// See [`ValueHL`] for a more high-level representation of arbitrary Marshal
/// structures.
#[derive(Debug, PartialEq)]
pub enum ValueLL {
    /// An instance of `nil`.
    Null,

    /// A Ruby boolean.
    Boolean(bool),

    /// A Ruby integer.
    ///
    /// This is guaranteed to be within the [-2<sup>30</sup>, 2<sup>30</sup> - 1] range.
    Integer(i32),

    /// A Ruby floating-point number.
    Float(f64),

    /// A Ruby array.
    Array(Vec<ValueLL>),

    /// A Ruby hash.
    Hash(Vec<(ValueLL, ValueLL)>),

    /// A Ruby symbol (as in `:foo`).
    Symbol(String),

    /// A Ruby byte array.
    ByteArray(Vec<u8>),

    /// A Ruby IVAR object.
    InstanceVariable(Box<InstanceVariable<ValueLL>>),

    /// A raw Ruby regular expression.
    ///
    /// Similar to [`RubyType::ByteArray`], but also contains the regular expression's flags.
    RawRegexp(RubyRegExpLL),

    /// A reference to an external class.
    ClassRef(String),

    /// A reference to an external module.
    ModuleRef(String),

    /// A Ruby object instance.
    Object(Box<RubyObject<ValueLL>>),

    /// User-defined marshalling data from a Ruby class with a `_dump` method.
    UserDef(UserDef),
}

impl<'de> FromRubyMarshal<'de> for ValueLL {
    fn deserialize(deserializer: &mut crate::de::Deserializer<'de>) -> Result<Self, ParsingError> {
        Ok(match deserializer.next_element()?.get() {
            RubyType::Null => ValueLL::Null,
            RubyType::True => ValueLL::Boolean(true),
            RubyType::False => ValueLL::Boolean(false),
            RubyType::Integer(x) => ValueLL::Integer(x),
            RubyType::Float(x) => ValueLL::Float(x),
            RubyType::Array(mut it) => {
                let mut v = Vec::with_capacity(it.size_hint());
                while let Some(element) = it.next_of_type()? {
                    v.push(element);
                }
                ValueLL::Array(v)
            }
            RubyType::Hash(mut it) => {
                let mut v = Vec::with_capacity(it.size_hint_pairs());
                while let (Some(a), Some(b)) =
                    (it.next_element_of_type()?, it.next_element_of_type()?)
                {
                    v.push((a, b));
                }
                ValueLL::Hash(v)
            }
            RubyType::Symbol(s) => ValueLL::Symbol(s.to_owned()),
            RubyType::ByteArray(a) => ValueLL::ByteArray(a.to_owned()),
            RubyType::InstanceVariable(iv) => {
                let (data, mut map_it) = iv.read_data_of_type()?;

                let mut v = Vec::with_capacity(map_it.size_hint_pairs());
                while let (Some(a), Some(b)) = (
                    map_it.next_element_of_type()?,
                    map_it.next_element_of_type()?,
                ) {
                    v.push((a, b));
                }

                ValueLL::InstanceVariable(Box::new(InstanceVariable { data, ivars: v }))
            }
            RubyType::RawRegexp(reg) => ValueLL::RawRegexp(RubyRegExpLL {
                data: reg.expr.to_owned(),
                flags: reg.flags,
            }),
            RubyType::ClassRef(s) => ValueLL::ClassRef(s.to_owned()),
            RubyType::ModuleRef(s) => ValueLL::ModuleRef(s.to_owned()),
            RubyType::Object(mut s) => {
                let mut v = Vec::with_capacity(s.fields.size_hint_pairs());
                while let (Some(a), Some(b)) = (
                    s.fields.next_element_of_type()?,
                    s.fields.next_element_of_type()?,
                ) {
                    v.push((a, b));
                }
                ValueLL::Object(Box::new(RubyObject {
                    class_name: s.class_name.to_owned(),
                    ivars: v,
                }))
            }
            RubyType::UserDef(ud) => ValueLL::UserDef(UserDef {
                class_name: ud.class_name.to_owned(),
                data: ud.data.to_owned(),
            }),
            RubyType::ObjectLink(_) => unreachable!(),
        })
    }
}

/// Represents any valid Ruby Marshal value (high-level).
///
/// Using this type as the target when trying to deserialize should always work
/// (as long as the data is not malformed) and will produce a tree of Ruby Marshal
/// values roughly corresponding to that of the original data (with symlinks and
/// object links resolved).
///
/// `ValueHL` seeks to be a middle-ground between direct deserialization into Rust
/// data structures lower-level representations of the Marshal format. It attempts
/// to decode strings into [`String`], and it provides a hand-written [`Debug`]
/// implementation that allows easier data exploration.
///
/// See [`ValueLL`] for a more low-level representation of arbitrary Marshal
/// structures.
#[derive(PartialEq)]
pub enum ValueHL {
    /// An instance of `nil`.
    Null,

    /// A Ruby boolean.
    Boolean(bool),

    /// A Ruby integer.
    ///
    /// This is guaranteed to be within the [-2<sup>30</sup>, 2<sup>30</sup> - 1] range.
    Integer(i32),

    /// A Ruby floating-point number.
    Float(f64),

    /// A Ruby array.
    Array(Vec<ValueHL>),

    /// A Ruby hash.
    Hash(Vec<(ValueHL, ValueHL)>),

    /// A Ruby symbol (as in `:foo`).
    Symbol(String),

    /// A Ruby byte array.
    ByteArray(Vec<u8>),

    /// A Ruby IVAR object.
    InstanceVariable(Box<InstanceVariable<ValueHL>>),

    /// A raw Ruby regular expression.
    ///
    /// Similar to [`RubyType::ByteArray`], but also contains the regular expression's flags.
    Regexp(RubyRegExpHL),

    /// A reference to an external class.
    ClassRef(String),

    /// A reference to an external module.
    ModuleRef(String),

    /// A Ruby object instance.
    Object(Box<RubyObject<ValueHL>>),

    /// User-defined marshalling data from a Ruby class with a `_dump` method.
    UserDef(UserDef),

    /// A Ruby string.
    String(String),
}

impl Debug for ValueHL {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Null => write!(f, "nil"),
            Self::Boolean(arg0) => arg0.fmt(f),
            Self::Integer(arg0) => arg0.fmt(f),
            Self::Float(arg0) => arg0.fmt(f),
            Self::Array(arg0) => arg0.fmt(f),
            Self::Hash(arg0) => f
                .debug_map()
                .entries(arg0.iter().map(|(k, v)| (k, v)))
                .finish(),
            Self::Symbol(arg0) => write!(f, ":{arg0}"),
            Self::ByteArray(arg0) => {
                if arg0.is_ascii() {
                    write!(f, "\"{}\"", String::from_utf8_lossy(arg0))
                } else {
                    write!(f, "{arg0:02x?}")
                }
            }
            Self::InstanceVariable(arg0) => f.debug_tuple("InstanceVariable").field(arg0).finish(),
            Self::Regexp(arg0) => arg0.fmt(f),
            Self::ClassRef(arg0) => f.debug_tuple("ClassRef").field(arg0).finish(),
            Self::ModuleRef(arg0) => f.debug_tuple("ModuleRef").field(arg0).finish(),
            Self::Object(arg0) => arg0.fmt(f),
            Self::UserDef(arg0) => f.debug_tuple("UserDef").field(arg0).finish(),
            Self::String(arg0) => arg0.fmt(f),
        }
    }
}

impl<'de> FromRubyMarshal<'de> for ValueHL {
    fn deserialize(deserializer: &mut crate::de::Deserializer<'de>) -> Result<Self, ParsingError> {
        if deserializer.peek_type_across_link()? == RubyTypeTag::InstanceVariable {
            {
                let mut checkpoint = deserializer.checkpoint();
                if let Ok(val) = String::deserialize(&mut checkpoint) {
                    checkpoint.commit();
                    return Ok(ValueHL::String(val));
                }
            }
            {
                let mut checkpoint = deserializer.checkpoint();
                if let Ok(val) = RubyRegExpHL::deserialize(&mut checkpoint) {
                    checkpoint.commit();
                    return Ok(ValueHL::Regexp(val));
                }
            }
        }
        Ok(match deserializer.next_element()?.get() {
            RubyType::Null => ValueHL::Null,
            RubyType::True => ValueHL::Boolean(true),
            RubyType::False => ValueHL::Boolean(false),
            RubyType::Integer(x) => ValueHL::Integer(x),
            RubyType::Float(x) => ValueHL::Float(x),
            RubyType::Array(mut it) => {
                let mut v = Vec::with_capacity(it.size_hint());
                while let Some(element) = it.next_of_type()? {
                    v.push(element);
                }
                ValueHL::Array(v)
            }
            RubyType::Hash(mut it) => {
                let mut v = Vec::with_capacity(it.size_hint_pairs());
                while let (Some(a), Some(b)) =
                    (it.next_element_of_type()?, it.next_element_of_type()?)
                {
                    v.push((a, b));
                }
                ValueHL::Hash(v)
            }
            RubyType::Symbol(s) => ValueHL::Symbol(s.to_owned()),
            RubyType::ByteArray(a) => ValueHL::ByteArray(a.to_owned()),
            RubyType::InstanceVariable(iv) => {
                let (data, mut map_it) = iv.read_data_of_type()?;

                let mut v = Vec::with_capacity(map_it.size_hint_pairs());
                while let (Some(a), Some(b)) = (
                    map_it.next_element_of_type()?,
                    map_it.next_element_of_type()?,
                ) {
                    v.push((a, b));
                }

                ValueHL::InstanceVariable(Box::new(InstanceVariable { data, ivars: v }))
            }
            RubyType::RawRegexp(reg) => ValueHL::Regexp(RubyRegExpHL {
                // HACK: we don't really know the regexp encoding at this point,
                // and if this didn't get caught in the type peeking, we never will... so...
                data: String::from_utf8_lossy(reg.expr).to_string(),
                flags: reg.flags,
            }),
            RubyType::ClassRef(s) => ValueHL::ClassRef(s.to_owned()),
            RubyType::ModuleRef(s) => ValueHL::ModuleRef(s.to_owned()),
            RubyType::Object(mut s) => {
                //println!("{}", s.class_name);
                let mut v = Vec::with_capacity(s.fields.size_hint_pairs());
                while let (Some(a), Some(b)) = (
                    s.fields.next_element_of_type()?,
                    s.fields.next_element_of_type()?,
                ) {
                    v.push((a, b));
                }
                ValueHL::Object(Box::new(RubyObject {
                    class_name: s.class_name.to_owned(),
                    ivars: v,
                }))
            }
            RubyType::UserDef(ud) => ValueHL::UserDef(UserDef {
                class_name: ud.class_name.to_owned(),
                data: ud.data.to_owned(),
            }),
            RubyType::ObjectLink(_) => unreachable!(),
        })
    }
}

#[derive(PartialEq, Eq)]

/// A structure that provides access to a Ruby IVAR (instance variable) object.
///
/// IVAR objects, in the Marshal data model, are containers over data that also provide
/// additional metadata in the form of a key-value store; the elements on the latter are
/// called "instance variables". Conceptually, they can be described as a boxed value
/// with a map attached.
pub struct InstanceVariable<Value>
where
    Value: Debug,
{
    /// The inner boxed data.
    pub data: Value,

    /// The read instance variables.
    pub ivars: Vec<(Value, Value)>,
}

impl<'de, Value> FromRubyMarshal<'de> for InstanceVariable<Value>
where
    Value: FromRubyMarshal<'de> + Debug,
{
    fn deserialize(deserializer: &mut crate::Deserializer<'de>) -> Result<Self, ParsingError> {
        if let RubyType::InstanceVariable(iv) = deserializer.next_element()?.get() {
            let (data, mut map_it) = iv.read_data_of_type()?;

            let mut v = Vec::with_capacity(map_it.size_hint_pairs());
            while let (Some(a), Some(b)) = (
                map_it.next_element_of_type()?,
                map_it.next_element_of_type()?,
            ) {
                v.push((a, b));
            }

            Ok(InstanceVariable { data, ivars: v })
        } else {
            Err(ParsingError::Message("expected ivar".to_string()))
        }
    }
}

impl<Value> Debug for InstanceVariable<Value>
where
    Value: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        struct DebugKeys<'a, Value: Debug>(&'a [(Value, Value)]);

        impl<'a, Value: Debug> Debug for DebugKeys<'a, Value> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_map()
                    .entries(self.0.iter().map(|(k, v)| (k, v)))
                    .finish()
            }
        }

        f.debug_struct("InstanceVariable")
            .field("data", &self.data)
            .field("ivars", &DebugKeys(&self.ivars))
            .finish()
    }
}

/// A raw Ruby regular expression (low-level).
#[derive(Debug, PartialEq, Eq)]
pub struct RubyRegExpLL {
    /// The underlying expression as a raw byte array.
    ///
    /// This would be the part of the regular expression that goes `/here/`.
    pub data: Vec<u8>,

    /// The flags of this regular expression.
    ///
    /// This is a bitfield with the following fields:
    ///
    /// | Mask   | Description                                                  |
    /// |--------|--------------------------------------------------------------|
    /// | `0x01` | `/i`: Matches are case insensitive.                          |
    /// | `0x02` | `/x` ("extended"): Ignore spaces and newlines in regexp.     |
    /// | `0x04` | `/m` ("multiline"): Newlines treated as any other character. |
    pub flags: u8, // TODO do a proper bitfield
}

/// A raw Ruby regular expression (high-level).
#[derive(PartialEq, Eq)]
pub struct RubyRegExpHL {
    /// The underlying expression as a raw byte array.
    ///
    /// This would be the part of the regular expression that goes `/here/`.
    pub data: String,

    /// The flags of this regular expression.
    ///
    /// This is a bitfield with the following fields:
    ///
    /// | Mask   | Description                                                  |
    /// |--------|--------------------------------------------------------------|
    /// | `0x01` | `/i`: Matches are case insensitive.                          |
    /// | `0x02` | `/x` ("extended"): Ignore spaces and newlines in regexp.     |
    /// | `0x04` | `/m` ("multiline"): Newlines treated as any other character. |
    pub flags: u8,
}

impl RubyRegExpHL {
    /// Returns whether the *ignore case* (`/i`) flag is set or not.
    pub fn ignore_case(&self) -> bool {
        (self.flags & 0x01) != 0
    }

    /// Returns whether the *extended* (`/x`) flag is set or not.
    pub fn extended(&self) -> bool {
        (self.flags & 0x02) != 0
    }

    /// Returns whether the *multiline* (`/m`) flag is set or not.
    pub fn multiline(&self) -> bool {
        (self.flags & 0x04) != 0
    }
}

impl Debug for RubyRegExpHL {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "/{}/{}{}{}",
            self.data,
            if self.multiline() { "m" } else { "" },
            if self.extended() { "x" } else { "" },
            if self.ignore_case() { "i" } else { "" }
        )
    }
}

#[derive(FromRubyMarshal)]
#[marshal(__crate_internal)]
struct RegExpRawIvar<'de> {
    #[marshal(ivar_data)]
    data: RubyRegexp<'de>,
    #[marshal(rename = "E")]
    encoding_short: Option<bool>,
    encoding: Option<&'de [u8]>,
}

impl<'de> FromRubyMarshal<'de> for RubyRegExpHL {
    fn deserialize(deserializer: &mut crate::Deserializer<'de>) -> Result<Self, ParsingError> {
        let regexp_ivar = RegExpRawIvar::deserialize(deserializer)?;

        if regexp_ivar.encoding_short.is_some() {
            // either true (UTF-8) or false (US-ASCII),
            // we can parse normally
            let data = std::str::from_utf8(regexp_ivar.data.expr)
                .map(ToOwned::to_owned)
                .map_err(|v| ParsingError::Message(v.to_string()))?;
            Ok(RubyRegExpHL {
                data,
                flags: regexp_ivar.data.flags,
            })
        } else if let Some(encoding) = regexp_ivar.encoding {
            let Some(encoding) = encoding_rs::Encoding::for_label_no_replacement(encoding) else {
                return Err(ParsingError::Message(format!("Unknown string encoding: {}", String::from_utf8_lossy(encoding))))
            };
            let mut decoder = encoding.new_decoder();
            let mut dst = String::with_capacity(
                decoder
                    .max_utf8_buffer_length(regexp_ivar.data.expr.len())
                    .expect("woah, that do be too big m8"),
            );

            let (result, _) =
                decoder.decode_to_string_without_replacement(regexp_ivar.data.expr, &mut dst, true);
            match result {
                encoding_rs::DecoderResult::InputEmpty => {},
                encoding_rs::DecoderResult::OutputFull => unreachable!(),
                encoding_rs::DecoderResult::Malformed(a, b) => {
                    return Err(ParsingError::Message(format!("Malformed byte sequence of {a} bytes (+ {b} consumed) while reading string")))
                },
            }
            Ok(RubyRegExpHL {
                data: dst,
                flags: regexp_ivar.data.flags,
            })
        } else {
            Err(ParsingError::Message(
                "No encoding provided for regular expression!".to_string(),
            ))
        }
    }
}

/// A Ruby object.
///
/// This is different from a Ruby IVAR object in that the boxed value
/// is always a symbol containing the name of the instanced class.
#[derive(PartialEq, Eq)]
pub struct RubyObject<Value: Debug> {
    /// The name of the class from which this object was instanced.
    pub class_name: String,

    /// The object's propperties.
    pub ivars: Vec<(Value, Value)>,
}

impl<Value: Debug> Debug for RubyObject<Value> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        struct DebugKeys<'a, Value: Debug>(&'a [(Value, Value)]);

        impl<'a, Value: Debug> Debug for DebugKeys<'a, Value> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_map()
                    .entries(self.0.iter().map(|(k, v)| (k, v)))
                    .finish()
            }
        }

        f.debug_struct("RubyObject")
            .field("class_name", &self.class_name)
            .field("ivars", &DebugKeys(&self.ivars))
            .finish()
    }
}

/// User-defined marshalling data from a Ruby class with a `_dump` method.
#[derive(PartialEq, Eq)]
pub struct UserDef {
    /// The name of the class from which this object was instanced.
    pub class_name: String,

    /// The raw data returned from the Ruby class's `_dump` method.
    pub data: Vec<u8>,
}

impl Debug for UserDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("UserDef")
            .field("class_name", &self.class_name)
            .field("data", &format_args!("[ ... {} bytes]", self.data.len()))
            .finish()
    }
}
