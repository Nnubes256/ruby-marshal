use alloc::{
    borrow::{Cow, ToOwned},
    collections::BTreeMap,
};
use core::{hash::Hash, marker::PhantomData, num::TryFromIntError};
use std::collections::HashMap;

use ruby_marshal_derive::FromRubyMarshal;

use super::{FromRubyMarshal, ParsingError, Result, RubyType, RubyTypeTag};

impl<'de> FromRubyMarshal<'de> for PhantomData<()> {
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        deserializer.skip_element()?;
        Ok(PhantomData)
    }
}

impl<'de> FromRubyMarshal<'de> for bool {
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        match deserializer.next_element()? {
            RubyType::True => Ok(true),
            RubyType::False => Ok(false),
            _ => Err(ParsingError::Message("Expected bool".to_string())),
        }
    }
}

macro_rules! impl_deserialize_for_num {
    ($($ty:ty)*) => {
        $(
            impl<'de> FromRubyMarshal<'de> for $ty {
                fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
                    let mut deserializer = deserializer.prepare()?;
                    match deserializer.next_element()? {
                        RubyType::Integer(x) => x
                            .try_into()
                            .map_err(|x: TryFromIntError| ParsingError::Message(x.to_string())),
                        _ => Err(ParsingError::Message(concat!("Expected ", stringify!($ty)).to_string())),
                    }
                }
            }
        )*
    }
}

impl_deserialize_for_num!(u8 u16 u32 u64 u128 i8 i16 usize isize);

impl<'de> FromRubyMarshal<'de> for i32 {
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        match deserializer.next_element()? {
            RubyType::Integer(x) => Ok(x),
            _ => Err(ParsingError::Message("Expected i32".to_string())),
        }
    }
}

impl<'de> FromRubyMarshal<'de> for i64 {
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        match deserializer.next_element()? {
            RubyType::Integer(x) => Ok(i64::from(x)),
            _ => Err(ParsingError::Message("Expected i64".to_string())),
        }
    }
}

impl<'de> FromRubyMarshal<'de> for i128 {
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        match deserializer.next_element()? {
            RubyType::Integer(x) => Ok(i128::from(x)),
            _ => Err(ParsingError::Message("Expected i128".to_string())),
        }
    }
}

// CLIPPY: Serde does the same if a f32 is found
#[allow(clippy::cast_possible_truncation)]
impl<'de> FromRubyMarshal<'de> for f32 {
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        match deserializer.next_element()? {
            RubyType::Float(x) => Ok(x as f32),
            _ => Err(ParsingError::Message("Expected i32".to_string())),
        }
    }
}

impl<'de> FromRubyMarshal<'de> for f64 {
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        match deserializer.next_element()? {
            RubyType::Float(x) => Ok(x),
            _ => Err(ParsingError::Message("Expected i32".to_string())),
        }
    }
}

impl<'de> FromRubyMarshal<'de> for &'de [u8] {
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        match deserializer.next_element()? {
            RubyType::ByteArray(a) => Ok(a),
            _ => Err(ParsingError::Message("Expected byte array".to_string())),
        }
    }
}

impl<'de, T> FromRubyMarshal<'de> for Option<T>
where
    T: FromRubyMarshal<'de>,
{
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        match deserializer.peek_type()? {
            RubyTypeTag::Null => {
                deserializer.skip_element()?; // which is null
                Ok(None)
            }
            _ => Ok(Some(T::deserialize(&mut deserializer)?)),
        }
    }
}

impl<'de, T> FromRubyMarshal<'de> for Vec<T>
where
    T: FromRubyMarshal<'de>,
{
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        match deserializer.next_element()? {
            RubyType::Array(mut it) => {
                let mut vec = Vec::with_capacity(it.size_hint());
                while let Some(el) = it.next_of_type(&mut deserializer)? {
                    vec.push(el);
                }
                Ok(vec)
            }
            _ => Err(ParsingError::Message("Expected vec".to_string())),
        }
    }
}

impl<'de, T, U> FromRubyMarshal<'de> for Vec<(T, U)>
where
    T: FromRubyMarshal<'de>,
    U: FromRubyMarshal<'de>,
{
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        match deserializer.next_element()? {
            RubyType::Hash(mut it) => {
                let mut vec = Vec::with_capacity(it.size_hint_pairs());
                while let (Some(key), Some(value)) = (
                    it.next_element_of_type(&mut deserializer)?,
                    it.next_element_of_type(&mut deserializer)?,
                ) {
                    vec.push((key, value));
                }
                Ok(vec)
            }
            _ => Err(ParsingError::Message("Expected vec".to_string())),
        }
    }
}

impl<'de, T> FromRubyMarshal<'de> for Box<T>
where
    T: FromRubyMarshal<'de>,
{
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        Ok(Box::new(T::deserialize(&mut deserializer)?))
    }
}

#[derive(FromRubyMarshal)]
#[marshal(__crate_internal)]
struct StringRaw<'de> {
    #[marshal(ivar_data)]
    data: &'de [u8],
    #[marshal(rename = "E")]
    encoding_short: Option<bool>,
    encoding: Option<&'de [u8]>,
}

impl<'de> FromRubyMarshal<'de> for String {
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        let string_ivar = StringRaw::deserialize(&mut deserializer)?;
        if string_ivar.encoding_short.is_some() {
            // either true (UTF-8) or false (US-ASCII),
            // we can parse normally
            std::str::from_utf8(string_ivar.data)
                .map(ToOwned::to_owned)
                .map_err(|v| ParsingError::Message(v.to_string()))
        } else if let Some(encoding) = string_ivar.encoding {
            let Some(encoding) = encoding_rs::Encoding::for_label_no_replacement(encoding) else {
                return Err(ParsingError::Message(format!("Unknown string encoding: {}", String::from_utf8_lossy(encoding))))
            };
            let mut decoder = encoding.new_decoder();
            let mut dst = String::with_capacity(
                decoder
                    .max_utf8_buffer_length(string_ivar.data.len())
                    .expect("woah, that do be too big m8"),
            );

            let (result, _) =
                decoder.decode_to_string_without_replacement(string_ivar.data, &mut dst, true);
            match result {
                encoding_rs::DecoderResult::InputEmpty => {},
                encoding_rs::DecoderResult::OutputFull => unreachable!(),
                encoding_rs::DecoderResult::Malformed(a, b) => {
                    return Err(ParsingError::Message(format!("Malformed byte sequence of {a} bytes (+ {b} consumed) while reading string")))
                },
            }
            Ok(dst)
        } else {
            Err(ParsingError::Message(
                "No encoding provided for string!".to_string(),
            ))
        }
    }
}

impl<'de> FromRubyMarshal<'de> for Cow<'de, str> {
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        let string_ivar = StringRaw::deserialize(&mut deserializer)?;
        if string_ivar.encoding_short.is_some() {
            // either true (UTF-8) or false (US-ASCII),
            // we can parse normally
            Ok(Cow::Borrowed(
                std::str::from_utf8(string_ivar.data)
                    .map_err(|v| ParsingError::Message(v.to_string()))?,
            ))
        } else if let Some(encoding) = string_ivar.encoding {
            let Some(encoding) = encoding_rs::Encoding::for_label_no_replacement(encoding) else {
                return Err(ParsingError::Message(format!("Unknown string encoding: {}", String::from_utf8_lossy(encoding))))
            };
            let mut decoder = encoding.new_decoder();
            let mut dst = String::with_capacity(
                decoder
                    .max_utf8_buffer_length(string_ivar.data.len())
                    .expect("woah, that do be too big m8"),
            );

            let (result, _) =
                decoder.decode_to_string_without_replacement(string_ivar.data, &mut dst, true);
            match result {
                encoding_rs::DecoderResult::InputEmpty => {},
                encoding_rs::DecoderResult::OutputFull => unreachable!(),
                encoding_rs::DecoderResult::Malformed(a, b) => {
                    return Err(ParsingError::Message(format!("Malformed byte sequence of {a} bytes (+ {b} consumed) while reading string")))
                },
            }
            Ok(Cow::Owned(dst))
        } else {
            Err(ParsingError::Message(
                "No encoding provided for string!".to_string(),
            ))
        }
    }
}

impl<'de, K, V, S: ::core::hash::BuildHasher + Default> FromRubyMarshal<'de> for HashMap<K, V, S>
where
    K: FromRubyMarshal<'de> + Eq + Hash,
    V: FromRubyMarshal<'de>,
{
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        match deserializer.next_element()? {
            RubyType::Hash(mut it) => {
                let mut map =
                    HashMap::with_capacity_and_hasher(it.size_hint_pairs(), Default::default());
                while let (Some(key), Some(value)) = (
                    it.next_element_of_type(&mut deserializer)?,
                    it.next_element_of_type(&mut deserializer)?,
                ) {
                    map.insert(key, value);
                }
                Ok(map)
            }
            _ => Err(ParsingError::Message("Expected map".to_string())),
        }
    }
}

impl<'de, K, V> FromRubyMarshal<'de> for BTreeMap<K, V>
where
    K: FromRubyMarshal<'de> + Ord,
    V: FromRubyMarshal<'de>,
{
    fn deserialize(deserializer: &mut super::Deserializer<'de>) -> Result<Self> {
        let mut deserializer = deserializer.prepare()?;
        match deserializer.next_element()? {
            RubyType::Hash(mut it) => {
                let mut map = BTreeMap::new();
                while let (Some(key), Some(value)) = (
                    it.next_element_of_type(&mut deserializer)?,
                    it.next_element_of_type(&mut deserializer)?,
                ) {
                    map.insert(key, value);
                }
                Ok(map)
            }
            _ => Err(ParsingError::Message("Expected map".to_string())),
        }
    }
}
