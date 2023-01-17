//! Deserialization of binary Marshal objects into Rust values.

use alloc::collections::BTreeSet;
use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
    str::{self, Utf8Error},
};

#[doc(hidden)]
pub mod impls;

/// The default recursion limit when deserializing.
///
/// This is used as the default when using [`ruby_marshal::from_bytes`](crate::from_bytes).
pub const DEFAULT_RECURSION_LIMIT: usize = 128;

/// The default maximum follow depth for object links found while deserializing.
///
/// This is used as the default when using [`ruby_marshal::from_bytes`](crate::from_bytes).
pub const DEFAULT_OBJECT_LINK_DEPTH_LIMIT: usize = 64;

/// Errors that may be generated when deserializing Marshal packed integers.
///
/// The specific error variants here are generated as part of [`ParsingError::InvalidPackedInteger`].
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum PackedIntegerError {
    /// Packed integer uses a variant specified as reserved.
    ///
    /// The only known case that this may happen is a packed integer where the first byte parsed is `5` or `-5` in
    /// two's complement (`i8`); this is invalid and is not known to happen on valid Marshal data.
    #[error("Packed integer uses a variant specified as reserved")]
    PackedIntegerReservedVariant,

    /// An overflow was detected while internal conversions were being performed.
    ///
    /// The bounds of a Ruby Marshal packed integer are [-2<sup>30</sup>, 2<sup>30</sup> - 1]. Anything beyond that
    /// is specified to be marshalled as a bignum.
    ///
    /// The bounds of an `i32` are [-2<sup>31</sup>, 2<sup>31</sup> - 1] (as [`i32::MIN`] and [`i32::MAX`] define),
    /// so normal parsing of a packed intger should not overflow an `i32`. Therefore, if a conversion overflow is detected;
    /// the parsed number is *probably* out-of-spec.
    #[error("Overflow detected while performing internal conversions; this number was probably generated out-of-spec")]
    ConverisonOverflow,
}

/// Errors that may be generated when deserializing.
///
/// The [`de::Result`](self::Result) type can be used defined as a shorthand for writing
/// a [`Result`](core::result::Result) with this type as error variant.
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ParsingError {
    /// Trailing data was left unparsed while deserializing.
    ///
    /// This error may be ignored by initializing a [`Deserializer`] manually instead of using
    /// the [`from_bytes`](crate::from_bytes)/[`from_bytes_with_options`](crate::from_bytes_with_options))
    /// convenience functions.
    #[error("Trailing data was left unparsed")]
    TrailingData,

    /// The deserializer found the end of the provided input data unexpectedly.
    #[error("End of file")]
    Eof,

    /// An unknown/unsupported type tag was found.
    #[error("Unknown type tag: {0}")]
    UnknownTag(u8),

    /// An invalid packed integer was found.
    ///
    /// Additional information about the cause of failure may be gained by reading the inner
    /// [`PackedIntegerError`].
    #[error("Invalid packed integer")]
    InvalidPackedInteger(#[from] PackedIntegerError),

    /// A floating-point number was found where the extra mantissa data was too long.
    ///
    /// On certain versions of Ruby, floating-point numbers that require a certain precision
    /// may, under certain circumstances, get marshalled with additional data attached
    /// containing between 1 and 4 of the last bytes of the mantissa. This *seems* to be used
    /// as a mechanism to ensure the floating point representation stays consistent across
    /// platforms.
    ///
    /// `ruby_marshal` can handle this correctly; however, the mantissa data may not be more
    /// than 4 bytes in size. This is an error; stock Ruby is not known to handle extra mantissa
    /// data of a larger size.
    #[error("While parsing a float, found a mantissa that is too long")]
    ParseFloatMantissaTooLong,

    /// A reference to a non-existant or not-yet-seen symbol was found.
    #[error("Symlink with index {0} was found while not being registered yet")]
    UnresolvedSymlink(usize),

    /// A reference to a non-existant or not-yet-seen object was found.
    #[error("Object link with index {0} was found while not being registered yet")]
    UnresolvedObjectLink(usize),

    /// A symbol reference where the index is negative or cannot fit into an `usize` was found.
    ///
    /// It is theoretically possible, but for now unproven, that symbol and object references
    /// can overflow the maximum integer size of an `i32` when being marshaled.
    ///
    /// Finding this on real data would imply a bug in the deserializer, so please report this
    /// on the issue tracker with a Ruby test case.
    #[error(
        "Edge case: negative symlink index, or index doesn't fit into an usize, please report: {0}"
    )]
    SymlinkIndexTooLarge(i32),

    /// An object reference where the index is negative or cannot fit into an `usize` was found.
    ///
    /// It is theoretically possible, but for now unproven, that symbol and object references
    /// can overflow the maximum integer size of an `i32` when being marshaled.
    ///
    /// Finding this on real data would imply a bug in the deserializer, so please report this
    /// on the issue tracker with a Ruby test case.
    #[error("Edge case: negative object link index, or index doesn't fit into an usize, please report: {0}")]
    ObjectLinkIndexTooLarge(i32),

    /// When reading the length of a variable-length data field, a negative length was found.
    ///
    /// A hint of the type that was being parsed at the time is provided.
    #[error("Unexpected negative length on {1:?}: {0}")]
    UnexpectedNegativeLength(i32, RubyTypeTag),

    /// A symbol was found that cannot be represented as a valid UTF-8 string.
    ///
    /// Ruby Symbols are assumed to be valid UTF-8. If this is not a correct assumption, please file
    /// a bug on the issue tracker with a Ruby test case.
    #[error("Invalid UTF-8 on symbol")]
    InvalidUtf8OnSymbol(Utf8Error),

    /// A class reference was found that cannot be represented as a valid UTF-8 string.
    ///
    /// Ruby class references are assumed to be valid UTF-8. If this is not a correct assumption, please file
    /// a bug on the issue tracker with a Ruby test case.
    #[error("Invalid UTF-8 on class reference")]
    InvalidUtf8OnClassRef(Utf8Error),

    /// A module reference was found that cannot be represented as a valid UTF-8 string.
    ///
    /// Ruby class references are assumed to be valid UTF-8. If this is not a correct assumption, please file
    /// a bug on the issue tracker with a Ruby test case.
    #[error("Invalid UTF-8 on module reference")]
    InvalidUtf8OnModuleRef(Utf8Error),

    /// The configured object link stack depth limit was exceeded.
    ///
    /// To parse objects across object links, a back-tracking stack is internally maintained.
    /// This error is returned whenever this stack exceeds the depth specified by
    /// [`DeserializerOptions#object_link_depth_limit`](`DeserializerOptions#object_link_depth_limit`)
    /// (by default configured as [`DEFAULT_OBJECT_LINK_DEPTH_LIMIT`]).
    #[error("Object link stack depth limit exceeded")]
    StackDepthLimitExceeded,

    /// The configured recursion limit was exceeded.
    ///
    /// Recursion is computed by tracking the amount of [`Frame`]s alive at a given point.
    /// This measure, while not exact, can be strongly correlated to the program call stack
    /// usage. This error will be returned whenever the number of [`Frame`]s in-flight exceeds
    /// the amount specified by [`DeserializerOptions#recursion_limit`](`DeserializerOptions#recursion_limit`)
    /// (by default configured as [`DEFAULT_RECURSION_LIMIT`]).
    #[error("Recursion limit exceeded")]
    RecursionLimitExceeded,

    /// An object reference was found within a [`Frame`] that itself is already handling an object reference.
    ///
    /// In order to correctly track deserialization across object references, a [`Frame`] should be created
    /// (by calling [`Deserializer#prepare`] every time an object which may contain an object link is deserialized.
    ///
    /// This can normally be resolved by ensuring any custom [`FromRubyMarshal`] implementations contain
    /// `let mut deserializer = deserializer.create_frame()?` at the top of the implementation, but if the implementation
    /// requires multiple nested calls to [`next_element`](`Frame#next_element`) then it may require inserting
    /// `let mut deserializer = deserializer.create_frame()?` for each call.
    #[error("Found a nested object link on the current frame; caller should insert an extra `deserializer.create_frame()?` in order to handle this condition")]
    DoubleObjectLink,

    /// Another kind of error was thrown, with the provided message.
    #[error("{0}")]
    Message(String),
}

/// Result type for errors thrown by the [`Deserializer`] or by [`FromRubyMarshal`] implementations.
///
/// This type can be used defined as a shorthand for writing a [`Result`](core::result::Result)
/// with [`ParsingError`] as error variant.
pub type Result<T> = ::core::result::Result<T, ParsingError>;

/// A data structure that can be deserialized from a binary Ruby Marshal object.
///
/// # Implementing `FromRubyMarshal`
///
/// The easiest way to implement `FromRubyMarshal` in many cases is to use the provided
/// [derive macro](ruby_marshal_derive::FromRubyMarshal):
///
/// ```
/// use ruby_marshal::{self, FromRubyMarshal};
///
/// #[derive(Debug, FromRubyMarshal)]
/// struct Test {
///     a: i32,
///     b: i32,
///     c: i32,
/// }
///
/// // Marshal.dump({:a => 1, :b => 2, :c => 3})
/// let input: &[u8] = &[
///     0x04, 0x08, 0x7b, 0x08, 0x3a, 0x06, 0x61, 0x69, 0x06, 0x3a, 0x06, 0x62, 0x69, 0x07, 0x3a,
///     0x06, 0x63, 0x69, 0x08,
/// ];
/// let out: Test = ruby_marshal::from_bytes(input).expect("Parsing failed");
/// assert_eq!(out.a, 1);
/// assert_eq!(out.b, 2);
/// assert_eq!(out.c, 3);
/// ```
///
/// However, more control may be desired from deserialization; in this case, one may implement
/// `FromRubyMarshal` manually.
///
/// - When handling arrays, maps, objects and IVAR objects, **always** either
///   fully consume them, or skip them.
///
///   ```
///   # use ruby_marshal::de::ParsingError;
///   # use ruby_marshal::de::{FromRubyMarshal, Deserializer, Result, RubyType};
///   # struct T;
///   #
///   # impl<'de> FromRubyMarshal<'de> for T {
///   #    fn deserialize(deserializer: &mut Deserializer<'de>) -> Result<Self> {
///   match deserializer.next_element()?.get() {
///       RubyType::Array(mut iter) => {
///           // WRONG: consume one element and then drop `iter`
///           let _ = iter.next();
///           //drop(iter);
///
///           // CORRECT: consume one element and then call iter.skip()
///           let _ = iter.next();
///           iter.skip();
///   #       Ok(T)
///       }
///   #   _ => Err(ParsingError::Message("test message".to_string()))
///   }
///   # }
///   # }
///   ```
pub trait FromRubyMarshal<'de>: Sized {
    /// Attempt to deserialize the incoming data from the provided [`Deserializer`].
    ///
    /// May return either an instance of `Self`, or a [`ParsingError`].
    fn deserialize(deserializer: &mut Deserializer<'de>) -> Result<Self>;
}

#[derive(Clone, Debug, PartialEq)]
enum ParsingState {
    Header,
    Element,
}

/// Additonal parameters that may be edited to customize the [`Deserializer`] behavior.
pub struct DeserializerOptions {
    /// Maximum recursion limit.
    ///
    /// Recursion is computed by tracking the amount of [`Frame`]s alive at a given point.
    /// This measure, while not exact, can be strongly correlated to the program call stack
    /// usage. The deserializer returns [`ParsingError::RecursionLimitExceeded`] whenever the number of
    /// [`Frame`]s in-flight exceeds the amount specified here.
    ///
    /// By default, [`DEFAULT_RECURSION_LIMIT`] is used.
    pub recursion_limit: usize,

    /// Maximum depth that may be reached by following object references,
    ///
    /// To parse objects across object links, a back-tracking stack is internally maintained.
    /// The deserializer returns [`ParsingError::StackDepthLimitExceeded`] whenever this stack
    /// exceeds the depth specified here.
    ///
    /// By default, [`DEFAULT_OBJECT_LINK_DEPTH_LIMIT`] is used.
    pub object_link_depth_limit: usize,
}

impl Default for DeserializerOptions {
    fn default() -> Self {
        Self {
            recursion_limit: DEFAULT_RECURSION_LIMIT,
            object_link_depth_limit: DEFAULT_OBJECT_LINK_DEPTH_LIMIT,
        }
    }
}

/// Maximum valid Marshal packed integer. Equal to -2<sup>30</sup>.
pub(crate) const MAX_MARSHAL_INTEGER: i32 = 1_073_741_823;

/// Minimum valid Marshal packed integer. Equal to 2<sup>30</sup> - 1.
pub(crate) const MIN_MARSHAL_INTEGER: i32 = -1_073_741_824;

/// A structure that deserializes binary Marshal objects into Rust values.
pub struct Deserializer<'de> {
    pub(crate) input: &'de [u8],
    state: ParsingState,
    stack: Vec<&'de [u8]>,
    checkpoints: Vec<&'de [u8]>,
    symbol_table: Vec<&'de str>,
    object_table: Vec<&'de [u8]>,
    blacklisted_objects: BTreeSet<&'de [u8]>,
    current_frame_depth: usize,
    max_frame_depth: usize,
    max_stack_depth: usize,
}

impl<'de> Deserializer<'de> {
    /// Creates an instance from the given input.
    ///
    /// # Example
    /// ```
    /// # use ruby_marshal::de::{FromRubyMarshal, Deserializer};
    ///
    /// let input = [0x04, 0x08, b'T']; // Marshal.dump(true)
    /// let mut deserializer = Deserializer::from_bytes(&input);
    /// let output = bool::deserialize(&mut deserializer);
    /// assert_eq!(output, Ok(true));
    /// ```
    pub fn from_bytes(input: &'de [u8]) -> Self {
        Deserializer {
            input,
            state: ParsingState::Header,
            stack: Vec::new(),
            checkpoints: Vec::new(),
            symbol_table: Vec::new(),
            object_table: Vec::new(),
            blacklisted_objects: BTreeSet::new(),
            current_frame_depth: 0,
            max_frame_depth: 128,
            max_stack_depth: 64,
        }
    }

    /// Creates an instance from the given input and providing additional options.
    ///
    /// # Example
    /// ```
    /// # use ruby_marshal::de::{
    /// #     FromRubyMarshal,
    /// #     Deserializer,
    /// #     DeserializerOptions,
    /// #     ParsingError
    /// # };
    /// use ruby_marshal::value::ValueHL;
    ///
    /// // Marshal.dump([[[[]]]])
    /// let input = [0x04, 0x08, b'[', 0x06, b'[', 0x06, b'[', 0x06, b'[', 0x00];
    ///
    /// let mut deserializer = Deserializer::from_bytes_with_options(&input, &Default::default());
    /// let output = ValueHL::deserialize(&mut deserializer);
    /// assert!(output.is_ok());
    ///
    /// let mut deserializer = Deserializer::from_bytes_with_options(
    ///     &input,
    ///     &DeserializerOptions {
    ///         recursion_limit: 2,
    ///         ..Default::default()
    ///     }
    /// );
    /// let output = ValueHL::deserialize(&mut deserializer);
    /// assert_eq!(output, Err(ParsingError::RecursionLimitExceeded));
    /// ```
    pub fn from_bytes_with_options(input: &'de [u8], options: &DeserializerOptions) -> Self {
        Deserializer {
            input,
            state: ParsingState::Header,
            stack: Vec::new(),
            checkpoints: Vec::new(),
            symbol_table: Vec::new(),
            object_table: Vec::new(),
            blacklisted_objects: BTreeSet::new(),
            current_frame_depth: 0,
            max_frame_depth: options.recursion_limit,
            max_stack_depth: options.object_link_depth_limit,
        }
    }

    /// Peeks the next type to parse without actually consuming the input.
    ///
    /// This method **will** follow object links.
    pub fn peek_type_across_link(&mut self) -> Result<RubyTypeTag> {
        self.ensure_version_read()?;
        let ret = self.peek_type()?;
        let ret = if ret == RubyTypeTag::ObjectLink {
            let mut checkpoint = self.checkpoint();
            let RawRubyType::ObjectLink(link) = checkpoint.parse_raw_element()? else {
                unreachable!();
            };
            checkpoint.jump_to_object_ref(link)?;
            let ret = checkpoint.peek_type()?;
            checkpoint.ret_from_object_ref();

            ret
            // returns to original state after here
        } else {
            ret
        };
        Ok(ret)
    }

    /// Peeks the next type to parse without actually consuming the input.
    ///
    /// This method **won't** follow object links.
    pub fn peek_type(&self) -> Result<RubyTypeTag> {
        match self.state {
            ParsingState::Header => {
                if self.input.len() < 2 {
                    return Err(ParsingError::Eof);
                }
                self.peek_raw_type_at_location(&self.input[2..])
            }
            ParsingState::Element => self.peek_raw_type_at_location(self.input),
        }
    }

    fn peek_raw_type_at_location(&self, input: &[u8]) -> Result<RubyTypeTag> {
        match input.first().copied().ok_or(ParsingError::Eof)? {
            b'0' => Ok(RubyTypeTag::Null),
            b'T' => Ok(RubyTypeTag::True),
            b'F' => Ok(RubyTypeTag::False),
            b'i' => Ok(RubyTypeTag::Integer),
            b'f' => Ok(RubyTypeTag::Float),
            b'[' => Ok(RubyTypeTag::Array),
            b'{' => Ok(RubyTypeTag::Hash),
            b':' => Ok(RubyTypeTag::Symbol),
            b';' => Ok(RubyTypeTag::Symlink),
            b'I' => Ok(RubyTypeTag::InstanceVariable),
            b'u' => Ok(RubyTypeTag::UserDef),
            b'\"' => Ok(RubyTypeTag::ByteArray),
            b'@' => Ok(RubyTypeTag::ObjectLink),
            b'/' => Ok(RubyTypeTag::RawRegexp),
            b'c' => Ok(RubyTypeTag::ClassRef),
            b'm' => Ok(RubyTypeTag::ModuleRef),
            b'o' => Ok(RubyTypeTag::Object),
            e => Err(ParsingError::UnknownTag(e)),
        }
    }

    fn peek_byte(&self) -> Result<u8> {
        self.input.first().copied().ok_or(ParsingError::Eof)
    }

    fn next_byte(&mut self) -> Result<u8> {
        let byte = self.peek_byte()?;
        self.input = &self.input[1..];
        Ok(byte)
    }

    fn next_bytes<const N: usize>(&mut self) -> Result<[u8; N]> {
        let mut ret = [0u8; N];
        for spot in &mut ret {
            *spot = self.next_byte()?;
        }
        Ok(ret)
    }

    fn next_bytes_dyn(&mut self, length: usize) -> Result<&'de [u8]> {
        if length > self.input.len() {
            return Result::Err(ParsingError::Eof);
        }

        let (ret, remaining) = self.input.split_at(length);
        self.input = remaining;
        Ok(ret)
    }

    fn next_u24_le(&mut self) -> Result<u32> {
        let mut ret = [0u8; 4];
        for spot in ret.iter_mut().take(3) {
            *spot = self.next_byte()?;
        }
        Ok(u32::from_le_bytes(ret))
    }

    fn read_type_tag(&mut self) -> Result<RubyTypeTag> {
        let byte = self.peek_type()?;
        //println!("{} {:?}", self.input.len(), byte);
        self.input = &self.input[1..];
        Ok(byte)
    }

    fn read_packed_integer(&mut self) -> Result<i32> {
        // The bounds of a Ruby Marshal packed integer are [-(2**30), 2**30 - 1], anything beyond that
        // gets serialized as a bignum.
        //
        // The bounds of an i32 are [-(2**31), 2**31 - 1], so we should be safe. Furthermore,
        // if a conversion overflow is detected; the parsed number is very much out-of-spec and
        // an error should be thrown.
        let b0 = i8::from_le_bytes([self.next_byte()?]);
        match b0 {
            0 => Ok(0),
            1 => Ok(i32::from(self.next_byte()?)),
            -1 => Ok(i32::from_ne_bytes(
                (0xFFFF_FF00u32 | u32::from(self.next_byte()?)).to_ne_bytes(),
            )),
            2 => Ok(i32::from(u16::from_le_bytes(self.next_bytes()?))),
            -2 => Ok(i32::from_ne_bytes(
                (0xFFFF_0000u32 | u32::from(u16::from_le_bytes(self.next_bytes::<2>()?)))
                    .to_ne_bytes(),
            )),
            3 => Ok(self
                .next_u24_le()?
                .try_into()
                .map_err(|_| PackedIntegerError::ConverisonOverflow)?),
            -3 => Ok(i32::from_ne_bytes(
                (0xFF00_0000u32 | self.next_u24_le()?).to_ne_bytes(),
            )),
            4 | -4 => {
                let out = i32::from_le_bytes(self.next_bytes::<4>()?);
                // TODO: this is a correctness check; add feature flag to conditionally
                // disable this behavior for performance.
                if (MIN_MARSHAL_INTEGER..=MAX_MARSHAL_INTEGER).contains(&out) {
                    Ok(out)
                } else {
                    Err(PackedIntegerError::ConverisonOverflow.into())
                }
            }
            5 | -5 => Err(PackedIntegerError::PackedIntegerReservedVariant.into()),
            x => Ok((i32::from(x).abs() - 5) * i32::from(x.signum())),
        }
    }

    fn read_float(&mut self) -> Result<f64> {
        let raw_length = self.read_packed_integer()?;
        let length = raw_length
            .try_into()
            .map_err(|_| ParsingError::UnexpectedNegativeLength(raw_length, RubyTypeTag::Float))?;
        let out = self.next_bytes_dyn(length)?;

        if let Some(terminator_idx) = out.iter().position(|v| *v == 0) {
            let (str, [0, mantissa @ ..]) = out.split_at(terminator_idx) else {
                unreachable!();
            };
            let float = str::parse::<f64>(&String::from_utf8_lossy(str))
                .map_err(|err| ParsingError::Message(err.to_string()))?;
            let transmuted = u64::from_ne_bytes(float.to_ne_bytes());
            if mantissa.len() > 4 {
                return Err(ParsingError::ParseFloatMantissaTooLong);
            }
            let (mantissa, mask) = mantissa.iter().fold((0u64, 0u64), |(acc, mask), v| {
                ((acc << 8) | u64::from(*v), (mask << 8) | 0xFF)
            });

            let transmuted = (transmuted & !mask) | mantissa;
            Ok(f64::from_ne_bytes(transmuted.to_ne_bytes()))
        } else {
            Ok(str::parse::<f64>(&String::from_utf8_lossy(out))
                .map_err(|err| ParsingError::Message(err.to_string()))?)
        }
    }

    #[allow(clippy::cast_sign_loss)]
    fn read_symbol(&mut self) -> Result<&'de str> {
        // FIXME: clippy::cast_sign_loss: What does Ruby do when you make like, *way* too many
        // object links?
        let length = self.read_packed_integer()? as usize;
        let out = self.next_bytes_dyn(length)?;

        let str = match str::from_utf8(out) {
            Ok(a) => a,
            Err(err) => return Err(ParsingError::InvalidUtf8OnSymbol(err)),
        };
        if self.stack.is_empty() {
            // Only update the symbol table if we are reading new data
            self.symbol_table.push(str);
        }
        Ok(str)
    }

    fn read_symlink(&mut self) -> Result<&'de str> {
        let raw_index = self.read_packed_integer()?;
        let index: usize = raw_index
            .try_into()
            .map_err(|_| ParsingError::SymlinkIndexTooLarge(raw_index))?;
        self.symbol_table
            .get(index)
            .copied()
            .ok_or(ParsingError::UnresolvedSymlink(index))
    }

    fn read_byte_string(&mut self) -> Result<&'de [u8]> {
        let raw_length = self.read_packed_integer()?;
        let length = raw_length.try_into().map_err(|_| {
            ParsingError::UnexpectedNegativeLength(raw_length, RubyTypeTag::ByteArray)
        })?;
        self.next_bytes_dyn(length)
    }

    fn read_regexp(&mut self) -> Result<RubyRegexp<'de>> {
        let expr = self.read_byte_string()?;
        let flags = self.next_byte()?;
        Ok(RubyRegexp { expr, flags })
    }

    fn read_classref(&mut self) -> Result<&'de str> {
        let raw_length = self.read_packed_integer()?;
        let length = raw_length.try_into().map_err(|_| {
            ParsingError::UnexpectedNegativeLength(raw_length, RubyTypeTag::ClassRef)
        })?;
        let out = self.next_bytes_dyn(length)?;

        str::from_utf8(out).map_err(ParsingError::InvalidUtf8OnClassRef)
    }

    fn read_moduleref(&mut self) -> Result<&'de str> {
        let raw_length = self.read_packed_integer()?;
        let length = raw_length.try_into().map_err(|_| {
            ParsingError::UnexpectedNegativeLength(raw_length, RubyTypeTag::ModuleRef)
        })?;
        let out = self.next_bytes_dyn(length)?;

        str::from_utf8(out).map_err(ParsingError::InvalidUtf8OnModuleRef)
    }

    fn read_array(&mut self) -> Result<RawRubyArrayIter> {
        let raw_length = self.read_packed_integer()?;
        let length = raw_length
            .try_into()
            .map_err(|_| ParsingError::UnexpectedNegativeLength(raw_length, RubyTypeTag::Array))?;
        Ok(RawRubyArrayIter {
            length,
            current_index: 0,
        })
    }

    fn read_hash(&mut self) -> Result<RawRubyMapIter> {
        let raw_length = self.read_packed_integer()?;
        let length = raw_length
            .try_into()
            .map_err(|_| ParsingError::UnexpectedNegativeLength(raw_length, RubyTypeTag::Hash))?;
        Ok(RawRubyMapIter {
            num_pairs: length,
            current_index: 0,
        })
    }

    fn read_object(&mut self) -> Result<RawRubyObject<'de>> {
        let class_name = if let RawRubyType::Symbol(sym) = self.next_raw_element()? {
            sym
        } else {
            return Err(ParsingError::Message(
                "expected class name as a symbol, got something else?".to_string(),
            ));
        };
        self.add_current_position_as_blacklisted();
        let fields = self.read_hash()?;
        Ok(RawRubyObject { class_name, fields })
    }

    fn read_userdef(&mut self) -> Result<RubyUserDef<'de>> {
        let class_name = if let RawRubyType::Symbol(sym) = self.next_raw_element()? {
            sym
        } else {
            return Err(ParsingError::Message(
                "expected class name as a symbol, got something else?".to_string(),
            ));
        };
        let data = self.read_byte_string()?;
        Ok(RubyUserDef { class_name, data })
    }

    /// Manually sets up the deserializer for further parsing.
    ///
    /// The deserializer ensures the header data is read, performs tracking of stack
    /// depth and follows object links if they are found. The provided [`Frame`] also ensures
    /// the deserializer returns from any followed object references once it is dropped.
    ///
    /// For object reference following to work, [`Frame`] **must** be used as a stand-in for this
    /// `Deserializer` until the current element has been fully parsed. Failure to do so may cause
    /// the deserializer to not being able to walk back from any followed object links, potentially
    /// resulting in parsing errors, inaccuracies and/or hangs.
    ///
    /// The easiest way to ensure this while implementing [`FromRubyMarshal`] is by shadowing
    /// the provided `Deserializer` using this method:
    ///
    /// ```
    /// # use ruby_marshal::de::{FromRubyMarshal, Deserializer};
    /// use ruby_marshal::de::Result;
    ///
    /// pub struct MyCustomData(/* ... */);
    ///
    /// impl<'de> FromRubyMarshal<'de> for MyCustomData {
    ///     fn deserialize(deserializer: &mut Deserializer<'de>) -> Result<Self> {
    ///         let mut deserializer = deserializer.create_frame()?;
    ///
    ///         // Now the deserializer is proxied through the created `Frame`,
    ///         // the following call to `deserializer.next_raw_element()` is safe.
    ///         // You can still use `T::deserialize(&mut deserializer)` to deserialize
    ///         // a subtype.
    ///
    ///         Ok(Self(/* ... */))
    ///
    ///         // The `Frame` is dropped here; if an object link was followed
    ///         // the parser returns to where it previously was.
    ///     }
    /// }
    /// ```
    ///
    ///
    pub fn create_frame<'deser>(&'deser mut self) -> Result<Frame<'de, 'deser>> {
        if self.current_frame_depth > self.max_frame_depth {
            return Err(ParsingError::RecursionLimitExceeded);
        }
        self.ensure_version_read()?;
        self.current_frame_depth += 1;
        let within_object_link = if self.peek_type()? == RubyTypeTag::ObjectLink {
            let RawRubyType::ObjectLink(link) = self.next_raw_element()? else {
                unreachable!();
            };

            self.jump_to_object_ref(link)?;
            true
        } else {
            false
        };
        Ok(Frame {
            inner: self,
            within_object_link,
        })
    }

    fn register_ref_in_object_table(&mut self, obj_ref: &'de [u8]) {
        // Only push into the object table if we are reading new input
        if !self.stack.is_empty() || self.position_blacklisted(obj_ref) {
            return;
        }
        self.object_table.push(obj_ref);
    }

    fn position_blacklisted(&self, obj_ref: &'de [u8]) -> bool {
        self.blacklisted_objects.contains(obj_ref)
    }

    fn add_current_position_as_blacklisted(&mut self) {
        //println!(" BLACKLIST {}", self.input.len());
        self.blacklisted_objects.insert(self.input);
    }

    pub(crate) fn jump_to_object_ref(&mut self, link: usize) -> Result<()> {
        //println!("CALL {link}");
        if self.stack.len() + 1 > self.max_stack_depth {
            return Err(ParsingError::StackDepthLimitExceeded);
        }
        let jump_target = self
            .object_table
            .get(link)
            .copied()
            .ok_or(ParsingError::UnresolvedObjectLink(link))?;
        self.stack.push(self.input);
        self.input = jump_target;
        Ok(())
    }

    pub(crate) fn ret_from_object_ref(&mut self) {
        //println!("RET");
        let jump_target = self.stack.pop().expect("jump stack pop while empty!");
        self.input = jump_target;
    }

    /// Create a checkpoint at the current input position.
    ///
    /// See [the documentation on `Checkpoint`](`Checkpoint`) for more details on
    /// how the checkpoint system works.
    pub fn checkpoint<'deser>(&'deser mut self) -> Checkpoint<'de, 'deser> {
        self.checkpoints.push(self.input);
        let symbol_table_bounds = self.symbol_table.len();
        let object_table_bounds = self.object_table.len();
        Checkpoint {
            inner: self,
            committed: false,
            symbol_table_bounds,
            object_table_bounds,
        }
    }

    fn pop_checkpoint(&mut self, symbol_table_bounds: usize, object_table_bounds: usize) {
        self.input = self.checkpoints.pop().expect("No checkpoints left!");
        self.symbol_table.truncate(symbol_table_bounds);
        self.object_table.truncate(object_table_bounds);
    }

    fn discard_checkpoint(&mut self) {
        self.checkpoints.pop().expect("No checkpoints left!");
    }

    fn parse_raw_element(&mut self) -> Result<RawRubyType<'de>> {
        let position_with_tag = <&[u8]>::clone(&self.input);
        match self.read_type_tag()? {
            RubyTypeTag::Null => Ok(RawRubyType::Null),
            RubyTypeTag::True => Ok(RawRubyType::True),
            RubyTypeTag::False => Ok(RawRubyType::False),
            RubyTypeTag::Integer => Ok(RawRubyType::Integer(self.read_packed_integer()?)),
            RubyTypeTag::Float => {
                self.register_ref_in_object_table(position_with_tag);
                Ok(RawRubyType::Float(self.read_float()?))
            }
            RubyTypeTag::Array => {
                self.register_ref_in_object_table(position_with_tag);
                Ok(RawRubyType::Array(self.read_array()?))
            }
            RubyTypeTag::Hash => {
                self.register_ref_in_object_table(position_with_tag);
                Ok(RawRubyType::Hash(self.read_hash()?))
            }
            RubyTypeTag::Symbol => Ok(RawRubyType::Symbol(self.read_symbol()?)),
            RubyTypeTag::Symlink => Ok(RawRubyType::Symbol(self.read_symlink()?)),
            RubyTypeTag::InstanceVariable => {
                self.register_ref_in_object_table(position_with_tag);
                Ok(RawRubyType::InstanceVariable(RawRubyIvar {
                    _private: PhantomData,
                }))
            }
            RubyTypeTag::UserDef => {
                self.register_ref_in_object_table(position_with_tag);
                Ok(RawRubyType::UserDef(self.read_userdef()?))
            }
            RubyTypeTag::ByteArray => {
                self.register_ref_in_object_table(position_with_tag);

                Ok(RawRubyType::ByteArray(self.read_byte_string()?))
            }
            RubyTypeTag::ObjectLink => {
                let raw_index = self.read_packed_integer()?;
                let index: usize = raw_index
                    .try_into()
                    .map_err(|_| ParsingError::ObjectLinkIndexTooLarge(raw_index))?;
                Ok(RawRubyType::ObjectLink(index))
            }
            RubyTypeTag::RawRegexp => {
                self.register_ref_in_object_table(position_with_tag);
                Ok(RawRubyType::RawRegexp(self.read_regexp()?))
            }
            RubyTypeTag::ClassRef => {
                self.register_ref_in_object_table(position_with_tag);
                Ok(RawRubyType::ClassRef(self.read_classref()?))
            }
            RubyTypeTag::ModuleRef => {
                self.register_ref_in_object_table(position_with_tag);
                Ok(RawRubyType::ModuleRef(self.read_moduleref()?))
            }
            RubyTypeTag::Object => {
                self.register_ref_in_object_table(position_with_tag);
                Ok(RawRubyType::Object(self.read_object()?))
            }
        }
    }

    pub fn next_raw_element(&mut self) -> Result<RawRubyType<'de>> {
        match self.state {
            ParsingState::Header => {
                self.next_byte()?;
                self.next_byte()?;
                self.state = ParsingState::Element;
                return self.next_raw_element();
            }
            ParsingState::Element => self.parse_raw_element(),
        }
    }

    pub fn next_element<'deser>(&'deser mut self) -> Result<RubyTypeGuard<'de, 'deser>> {
        if self.current_frame_depth > self.max_frame_depth {
            return Err(ParsingError::RecursionLimitExceeded);
        }
        match self.state {
            ParsingState::Header => {
                self.next_byte()?;
                self.next_byte()?;
                self.state = ParsingState::Element;
                return self.next_element();
            }
            ParsingState::Element => {
                let mut within_object_link = false;
                let raw = self.parse_raw_element()?;
                let element = if let RawRubyType::ObjectLink(link) = raw {
                    // TODO handle nested
                    self.jump_to_object_ref(link)?;
                    within_object_link = true;
                    self.parse_raw_element()?
                } else {
                    raw
                };

                self.current_frame_depth += 1;
                Ok(RubyTypeGuard {
                    inner: element,
                    deserializer: self,
                    within_object_link,
                })
            }
        }
    }

    /// Skips the next element.
    ///
    /// This can be more efficent than discarding the result of [`Frame#next_element()`],
    /// since it also skips following object links.
    ///
    /// At the type level, `PhantomData<()>` provides the same behavior.
    pub fn skip_element(&mut self) -> Result<()> {
        match self.state {
            ParsingState::Header => {
                self.next_byte()?;
                self.next_byte()?;
                self.state = ParsingState::Element;
                return self.skip_element();
            }
            ParsingState::Element => match self.parse_raw_element()? {
                RawRubyType::Array(it) => it.skip(self)?,
                RawRubyType::Hash(it) => it.skip(self)?,
                RawRubyType::InstanceVariable(iv) => iv.skip(self)?,
                RawRubyType::Object(obj) => obj.skip(self)?,
                _ => (),
            },
        }
        Ok(())
    }

    fn ensure_version_read(&mut self) -> Result<()> {
        match self.state {
            ParsingState::Header => {
                self.next_byte()?;
                self.next_byte()?;
                self.state = ParsingState::Element;
                Ok(())
            }
            ParsingState::Element => Ok(()),
        }
    }
}

pub struct RubyTypeGuard<'de, 'deser> {
    inner: RawRubyType<'de>,
    deserializer: &'deser mut Deserializer<'de>,
    within_object_link: bool,
}

impl<'de, 'deser> RubyTypeGuard<'de, 'deser> {
    pub fn get<'a>(&'a mut self) -> RubyType<'de, 'a> {
        RubyType::from_raw(self.inner.clone(), self.deserializer)
    }
}

impl<'de, 'deser> Drop for RubyTypeGuard<'de, 'deser> {
    fn drop(&mut self) {
        if self.within_object_link {
            self.deserializer.ret_from_object_ref();
        }
        self.deserializer.current_frame_depth -= 1;
    }
}

/// A stack guard used to read data from a [`Deserializer`].
///
/// `Frame`s are used on [`FromRubyMarshal`] implementations to ensure:
///
/// 1. That object references are correctly handled
/// 2. That the configured recursion depth is not exceeded.
///
/// A `Frame` may be obtained by calling [`Deserializer::create_frame()`]. Once obtained, it is meant
/// to be used as a stand-in of the parent [`Deserializer`] until the element is fully read.
///
/// # Implementation considerations
///
/// - If using [`Frame`], create the [`Frame`] before doing any deserializing. The best way to do this
///   is by inserting a [`Deserializer::create_frame()`] call on the first line that shadows the provided
///   deserializer:
///
///   ```
///   # struct T;
///   use ruby_marshal::de::{FromRubyMarshal, Deserializer, Result};
///
///   impl<'de> FromRubyMarshal<'de> for T {
///       fn deserialize(deserializer: &mut Deserializer<'de>) -> Result<Self> {
///           let mut deserializer = deserializer.create_frame()?; // <-- add this before
///                                                           //     doing anything
///
///           // ...you may now start deserializing...
///   #       Ok(T)
///       }
///   }
///   ```
///
/// - If deserializing multiple elements within the same function, it can be wise to
///   create additional frames in between.
///
///   ```
///   # struct T;
///   # use ruby_marshal::de::ParsingError;
///   use ruby_marshal::de::{FromRubyMarshal, Deserializer, Result, RawRubyType};
///
///   impl<'de> FromRubyMarshal<'de> for T {
///       fn deserialize(deserializer: &mut Deserializer<'de>) -> Result<Self> {
///           let mut deserializer = deserializer.create_frame()?; // <-- first frame
///
///           match deserializer.next_raw_element()? {
///               RawRubyType::Array(mut iter) => {
///                   // second frame, now parent of the first frame
///                   let mut deserializer = deserializer.create_frame()?;
///
///                   // ...you can now safely deserialize the array inline...
///   #               Ok(T)
///               }
///               // ...
///   #           _ => Err(ParsingError::Message("test message".to_string()))
///           }
///       }
///   }
///   ```
///
pub struct Frame<'de, 'deser> {
    inner: &'deser mut Deserializer<'de>,
    within_object_link: bool,
}

impl<'de, 'deser> Deref for Frame<'de, 'deser> {
    type Target = Deserializer<'de>;

    fn deref(&self) -> &Self::Target {
        self.inner
    }
}

impl<'de, 'deser> DerefMut for Frame<'de, 'deser> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner
    }
}

impl<'de, 'deser> Frame<'de, 'deser> {
    /// Reads the next element from the input data.
    pub fn next_element<'a>(&'a mut self) -> Result<RubyType<'de, 'a>> {
        let ret = self.inner.next_raw_element()?;
        if let RawRubyType::ObjectLink(link) = ret {
            if self.within_object_link {
                return Err(ParsingError::DoubleObjectLink);
            }
            self.inner.jump_to_object_ref(link)?;
            self.within_object_link = true;
            self.next_element()
        } else {
            Ok(RubyType::from_raw(ret, self.inner))
        }
    }
}

impl<'de, 'deser> Drop for Frame<'de, 'deser> {
    fn drop(&mut self) {
        if self.within_object_link {
            self.inner.ret_from_object_ref();
        }
        self.inner.current_frame_depth -= 1;
    }
}

/// A drop guard which allows fallible deserialization of complex types.
///
/// A `Checkpoint` is instantiated with the current position in the input data. When a `Checkpoint` is
/// dropped, it will restore its parent `Deserializer` to the state when the `Checkpoint` was created,
/// unless [`Checkpoint::commit()`] is called first. This allows a [`FromRubyMarshal`] implementation to
/// provide fallible deserialization.
///
/// A `Checkpoint` may be obtained by calling [`Deserializer::checkpoint()`]. Once obtained,
/// it is meant to be used as a stand-in of the parent [`Deserializer`] until it is dropped.
///
/// # Example
///
/// ```
/// # use ruby_marshal::de::{FromRubyMarshal, Deserializer, ParsingError, RubyTypeTag};
/// use ruby_marshal::value::{ValueLL, InstanceVariable};
/// use ruby_marshal::de::Result;
///
/// #[derive(Debug, PartialEq)]
/// pub enum StringOrOtherIvar {
///     String(String),
///     Ivar(InstanceVariable<ValueLL>)
/// }
///
/// impl<'de> FromRubyMarshal<'de> for StringOrOtherIvar {
///     fn deserialize(deserializer: &mut Deserializer<'de>) -> Result<Self> {
///         // Strings on Ruby are instance variables too, so we gotta
///         // first test if deserializing a `String` succeeds.
///         if deserializer.peek_type_across_link()? == RubyTypeTag::InstanceVariable {
///             {
///                 // To test this safely, we can create a checkpoint here...
///                 let mut checkpoint = deserializer.checkpoint();
///
///                 // ...and then deserialize as normal, passing in the
///                 // checkpoint as a stand-in to Deserializer
///                 // (similar to `Frame`).
///                 if let Ok(val) = String::deserialize(&mut checkpoint) {
///                     // If it succeeds, that means it was indeed a string,
///                     // so we "commit" the checkpoint; i.e. we mark this
///                     // deserialization path as the correct one.
///                     checkpoint.commit();
///                     return Ok(Self::String(val));
///                 }
///
///                 // If it fails though, we will want to try deserializing the
///                 // instance variable again with another `FromRubyMarshal`
///                 // implementation. Fortunately...
///             }
///             // ...we didn't ask the checkpoint to commit on the failure case,
///             // so by the time we get here, it has rolled back the deserializer
///             // to where we were before. Now we can try the other variant:
///             return Ok(Self::Ivar(InstanceVariable::deserialize(deserializer)?))
///         } else {
///             return Err(ParsingError::Message("expected ivar".to_string()));
///         }
///     }
/// }
///
/// fn main() {
///     // Marshal.dump("foo")
///     let input_string = [
///         0x04, 0x08,
///         b'I', // <-- indicates an IVAR follows
///         b'"', 0x08, b'f', b'o', b'o',
///         0x06, b':', 0x06, b'E', b'T'
///     ];
///
///     let output: Result<StringOrOtherIvar> =
///         ruby_marshal::from_bytes(&input_string);
///     assert_eq!(output, Ok(StringOrOtherIvar::String("foo".to_string())));
///
///     // Marshal.dump(/foo/i)
///     let input_regexp = [
///         0x04, 0x08,
///         b'I', // <-- indicates an IVAR follows
///         b'/', 0x08, b'f', b'o', b'o', 0x01,
///         0x06, b':', 0x06, b'E', b'F'
///     ];
///
///     let output: Result<StringOrOtherIvar> =
///         ruby_marshal::from_bytes(&input_regexp);
///     assert!(matches!(output, Ok(StringOrOtherIvar::Ivar(_))));
/// }
/// ```
pub struct Checkpoint<'de, 'deser> {
    inner: &'deser mut Deserializer<'de>,
    committed: bool,
    symbol_table_bounds: usize,
    object_table_bounds: usize,
}

impl<'de, 'deser> Deref for Checkpoint<'de, 'deser> {
    type Target = Deserializer<'de>;

    fn deref(&self) -> &Self::Target {
        self.inner
    }
}

impl<'de, 'deser> DerefMut for Checkpoint<'de, 'deser> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner
    }
}

impl<'de, 'deser> Checkpoint<'de, 'deser> {
    /// Used to indicate this `Checkpoint` that it should *not* roll back on Drop.
    ///
    /// Calling `commit` indicates that the current deserialization path has been
    /// validated as correct, and thus the deserializer should act as if the checkpoint
    /// was never created. After calling `commit`, dropping the `Checkpoint` will
    /// become a no-op.
    pub fn commit(mut self) {
        self.inner.discard_checkpoint();
        self.committed = true;
    }
}

impl<'de, 'deser> Drop for Checkpoint<'de, 'deser> {
    fn drop(&mut self) {
        if !self.committed {
            self.inner
                .pop_checkpoint(self.symbol_table_bounds, self.object_table_bounds);
        }
    }
}

/// A Ruby type extracted from the marshalled data.
#[non_exhaustive]
pub enum RubyType<'de, 'deser> {
    /// An instance of `nil`.
    Null,

    /// An instance of `true`.
    True,

    /// An instance of `false`.
    False,

    /// A Ruby integer.
    ///
    /// This is guaranteed to be within the [-2<sup>30</sup>, 2<sup>30</sup> - 1] range.
    Integer(i32),

    /// A Ruby floating-point number.
    Float(f64),

    /// A Ruby array.
    ///
    /// Use the underlying [`RubyArrayIter`] to access its elements.
    Array(RubyArrayIter<'de, 'deser>),

    /// A Ruby hash.
    ///
    /// Use the underlying [`RubyMapIter`] to access its elements.
    ///
    /// **IMPORTANT: You must either fully consume or skip the map before dropping
    /// the provided [`RubyMapIter`]; the deserializer does not track how far into
    /// the map it has has advanced.**
    Hash(RubyMapIter<'de, 'deser>),

    /// A Ruby symbol (as in `:foo`).
    Symbol(&'de str),

    /// A Ruby byte array.
    ByteArray(&'de [u8]),

    /// A Ruby IVAR (instance variable) object.
    ///
    /// Use the underlying [`RubyIvar`] to access the inner data and attached metadata
    /// fields.
    ///
    /// **IMPORTANT: You must either fully consume or skip the IVAR before dropping
    /// the provided [`RubyIvar`]; the deserializer does not track how far into
    /// the map it has has advanced.**
    InstanceVariable(RubyIvar<'de, 'deser>),

    /// A raw Ruby regular expression.
    ///
    /// Similar to [`RubyType::ByteArray`], but also contains the regular expression's flags.
    RawRegexp(RubyRegexp<'de>),

    /// A reference to an external class.
    ClassRef(&'de str),

    /// A reference to an external module.
    ModuleRef(&'de str),

    /// A Ruby object instance.
    ///
    /// Use the underlying [`RubyObject`] and its [`RubyMapIter`] to access the class name
    /// and properties of the instance.
    ///
    /// **IMPORTANT: You must either fully consume or skip the object before dropping
    /// the provided [`RubyObject`]; the deserializer does not track how far into
    /// the object's properties map it has has advanced.**
    Object(RubyObject<'de, 'deser>),

    /// A reference to a previously-parsed Ruby object.
    ///
    /// The deserializer internally tracks which object links correspond to what positions
    /// in the input data and sets itself up to parse the underlying objects transparently.
    ///
    /// In most cases you should not hit this; if you do, you either forgot to insert a
    /// `let mut deserializer = deserializer.create_frame()?;` line before retrieving an element,
    /// or the deserializer has a bug.
    ObjectLink(usize),

    /// User-defined marshalling data from a Ruby class with a `_dump` method.
    UserDef(RubyUserDef<'de>),
}

impl<'de, 'deser> RubyType<'de, 'deser> {
    pub fn from_raw(raw: RawRubyType<'de>, deserializer: &'deser mut Deserializer<'de>) -> Self {
        match raw {
            RawRubyType::Null => RubyType::Null,
            RawRubyType::True => RubyType::True,
            RawRubyType::False => RubyType::False,
            RawRubyType::Integer(x) => RubyType::Integer(x),
            RawRubyType::Float(x) => RubyType::Float(x),
            RawRubyType::Array(x) => RubyType::Array(RubyArrayIter::from_raw(x, deserializer)),
            RawRubyType::Hash(x) => RubyType::Hash(RubyMapIter::from_raw(x, deserializer)),
            RawRubyType::Symbol(x) => RubyType::Symbol(x),
            RawRubyType::ByteArray(x) => RubyType::ByteArray(x),
            RawRubyType::InstanceVariable(x) => {
                RubyType::InstanceVariable(RubyIvar::from_raw(x, deserializer))
            }
            RawRubyType::RawRegexp(x) => RubyType::RawRegexp(x),
            RawRubyType::ClassRef(x) => RubyType::ClassRef(x),
            RawRubyType::ModuleRef(x) => RubyType::ModuleRef(x),
            RawRubyType::Object(x) => RubyType::Object(RubyObject::from_raw(x, deserializer)),
            RawRubyType::ObjectLink(x) => RubyType::ObjectLink(x),
            RawRubyType::UserDef(x) => RubyType::UserDef(x),
        }
    }
}

/// A Ruby type extracted from the marshalled data (without built-in deserializer).
#[non_exhaustive]
#[derive(Clone)]
pub enum RawRubyType<'de> {
    /// An instance of `nil`.
    Null,

    /// An instance of `true`.
    True,

    /// An instance of `false`.
    False,

    /// A Ruby integer.
    ///
    /// This is guaranteed to be within the [-2<sup>30</sup>, 2<sup>30</sup> - 1] range.
    Integer(i32),

    /// A Ruby floating-point number.
    Float(f64),

    /// A Ruby array.
    ///
    /// Use the underlying [`RawRubyArrayIter`] to access its elements.
    ///
    /// **IMPORTANT: You must either fully consume or skip the array before dropping
    /// the provided [`RawRubyArrayIter`]; the deserializer does not track how far into
    /// the array it has has advanced.**
    Array(RawRubyArrayIter),

    /// A Ruby hash.
    ///
    /// Use the underlying [`RawRubyMapIter`] to access its elements.
    ///
    /// **IMPORTANT: You must either fully consume or skip the map before dropping
    /// the provided [`RawRubyMapIter`]; the deserializer does not track how far into
    /// the map it has has advanced.**
    Hash(RawRubyMapIter),

    /// A Ruby symbol (as in `:foo`).
    Symbol(&'de str),

    /// A Ruby byte array.
    ByteArray(&'de [u8]),

    /// A Ruby IVAR (instance variable) object.
    ///
    /// Use the underlying [`RubyIvar`] to access the inner data and attached metadata
    /// fields.
    ///
    /// **IMPORTANT: You must either fully consume or skip the IVAR before dropping
    /// the provided [`RubyIvar`]; the deserializer does not track how far into
    /// the map it has has advanced.**
    InstanceVariable(RawRubyIvar),

    /// A raw Ruby regular expression.
    ///
    /// Similar to [`RubyType::ByteArray`], but also contains the regular expression's flags.
    RawRegexp(RubyRegexp<'de>),

    /// A reference to an external class.
    ClassRef(&'de str),

    /// A reference to an external module.
    ModuleRef(&'de str),

    /// A Ruby object instance.
    ///
    /// Use the underlying [`RubyObject`] and its [`RubyMapIter`] to access the class name
    /// and properties of the instance.
    ///
    /// **IMPORTANT: You must either fully consume or skip the object before dropping
    /// the provided [`RubyObject`]; the deserializer does not track how far into
    /// the object's properties map it has has advanced.**
    Object(RawRubyObject<'de>),

    /// A reference to a previously-parsed Ruby object.
    ///
    /// The deserializer internally tracks which object links correspond to what positions
    /// in the input data and sets itself up to parse the underlying objects transparently.
    ///
    /// In most cases you should not hit this; if you do, you either forgot to insert a
    /// `let mut deserializer = deserializer.create_frame()?;` line before retrieving an element,
    /// or the deserializer has a bug.
    ObjectLink(usize),

    /// User-defined marshalling data from a Ruby class with a `_dump` method.
    UserDef(RubyUserDef<'de>),
}

/// Ruby type tags that may be found while deserializing.
///
/// Essentially, a shallow version of [`RubyType`].
#[derive(Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum RubyTypeTag {
    /// An instance of `nil`.
    Null,

    /// An instance of `true`.
    True,

    /// An instance of `false`.
    False,

    /// A Ruby integer.
    ///
    /// This is guaranteed to be within the [-2<sup>30</sup>, 2<sup>30</sup> - 1] range.
    Integer,

    /// A Ruby floating-point number.
    Float,

    /// A Ruby array.
    Array,

    /// A Ruby hash.
    Hash,

    /// A Ruby symbol (as in `:foo`).
    Symbol,

    /// A reference to a previously-found Ruby symbol.
    ///
    /// When retrieving a [`RubyType`] at this position, the deserializer will
    /// attempt to resolve the underlying symbol and provide it instead.
    /// Thus, `Symlink` will either result in a [`RubyType::Symbol`] or
    /// in [`ParsingError::UnresolvedSymlink`] when retrieving the next element.
    Symlink,

    /// A Ruby byte array.
    ByteArray,

    /// A Ruby IVAR object (see [`RubyIvar`]).
    InstanceVariable,

    /// A raw Ruby regular expression.
    ///
    /// Similar to [`RubyType::ByteArray`], but also contains the regular expression's flags.
    RawRegexp,

    /// A reference to an external class.
    ClassRef,

    /// A reference to an external module.
    ModuleRef,

    /// A Ruby object instance.
    Object,

    /// A reference to a previously-parsed Ruby object.
    ///
    /// The deserializer internally tracks which object links correspond to what positions
    /// in the input data and sets itself up to parse the underlying objects transparently.
    ///
    /// In most cases you should not hit this; if you do, you either forgot to insert a
    /// `let mut deserializer = deserializer.create_frame()?;` line before retrieving an element,
    /// or the deserializer has a bug.
    ObjectLink,

    /// User-defined marshalling data from a Ruby class with a `_dump` method.
    UserDef,
}

/// A lending iterator over the elements of a Ruby array (raw API)
///
/// **IMPORTANT: You must either fully consume or skip this iterator before dropping it;
/// the deserializer does not track how far into the array it has has advanced.**
#[derive(Clone)]
pub struct RawRubyArrayIter {
    length: usize,
    current_index: usize,
}

impl RawRubyArrayIter {
    /// Consumes and returns the next element as a [`RawRubyType`].
    ///
    /// Returns `Some(element)` if an element was deserialized, or `None` if the
    /// iterator has been fully exhausted.
    pub fn next<'de>(
        &mut self,
        deserializer: &mut Deserializer<'de>,
    ) -> Result<Option<RawRubyType<'de>>> {
        if self.current_index >= self.length {
            return Ok(None);
        }

        let next = deserializer.next_raw_element()?;
        self.current_index += 1;
        Ok(Some(next))
    }

    /// Consumes and returns the next element as a `T` implementing [`FromRubyMarshal`].
    ///
    /// Returns `Some(data)` if an element was deserialized, or `None` if the
    /// iterator has been fully exhausted.
    pub fn next_of_type<'de, T: FromRubyMarshal<'de>>(
        &mut self,
        deserializer: &mut Deserializer<'de>,
    ) -> Result<Option<T>> {
        if self.current_index >= self.length {
            return Ok(None);
        }

        let next = T::deserialize(deserializer)?;
        self.current_index += 1;
        Ok(Some(next))
    }

    /// Skips the remaining elements of the array.
    ///
    /// This can be more efficent than calling [`RubyArrayIter::next()`]/[`RubyArrayIter::next_of_type()`].
    pub fn skip(mut self, deserializer: &mut Deserializer) -> Result<()> {
        self.skip_impl(deserializer)
    }

    pub(crate) fn skip_impl(&mut self, deserializer: &mut Deserializer) -> Result<()> {
        if self.current_index >= self.length {
            return Ok(());
        }

        while self.current_index < self.length {
            deserializer.skip_element()?;
            self.current_index += 1;
        }

        Ok(())
    }

    /// Returns the total size of the array.
    pub fn size_hint(&self) -> usize {
        self.length
    }
}

/// A lending iterator over the elements of a Ruby array.
///
/// **IMPORTANT: You must either fully consume or skip this iterator before dropping it;
/// the deserializer does not track how far into the array it has has advanced.**
pub struct RubyArrayIter<'de: 'deser, 'deser> {
    inner: RawRubyArrayIter,
    deserializer: &'deser mut Deserializer<'de>,
}

impl<'de: 'deser, 'deser> RubyArrayIter<'de, 'deser> {
    pub fn from_raw(raw: RawRubyArrayIter, deserializer: &'deser mut Deserializer<'de>) -> Self {
        Self {
            inner: raw,
            deserializer,
        }
    }

    /// Consumes and returns the next element as a [`RubyType`].
    ///
    /// Returns `Some(element)` if an element was deserialized, or `None` if the
    /// iterator has been fully exhausted.
    pub fn next<'deser_new>(&'deser_new mut self) -> Result<Option<RubyType<'de, 'deser_new>>> {
        if self.inner.current_index >= self.inner.length {
            return Ok(None);
        }

        let next = self.deserializer.next_raw_element()?;
        self.inner.current_index += 1;
        Ok(Some(RubyType::from_raw(next, self.deserializer)))
    }

    /// Consumes and returns the next element as a `T` implementing [`FromRubyMarshal`].
    ///
    /// Returns `Some(data)` if an element was deserialized, or `None` if the
    /// iterator has been fully exhausted.
    pub fn next_of_type<T: FromRubyMarshal<'de>>(&mut self) -> Result<Option<T>> {
        self.inner.next_of_type(self.deserializer)
    }

    /// Skips the remaining elements of the array.
    ///
    /// This can be more efficent than calling [`RubyArrayIter::next()`]/[`RubyArrayIter::next_of_type()`].
    pub fn skip(mut self) -> Result<()> {
        self.inner.skip_impl(self.deserializer)
    }

    /// Returns the total size of the array.
    pub fn size_hint(&self) -> usize {
        self.inner.size_hint()
    }
}

/// A lending iterator over the elements of a Ruby hash (raw API).
///
/// **IMPORTANT: You must either fully consume or skip this iterator before dropping it;
/// the deserializer does not track how far into the map it has has advanced.**
#[derive(Clone)]
pub struct RawRubyMapIter {
    num_pairs: usize,
    current_index: usize,
}

impl RawRubyMapIter {
    /// **DO NOT USE:** this method is misleading and cannot be fixed, and it will be removed
    /// on the next minor release. Use [`RubyMapIter::next_element`] instead, ensuring
    /// you fully consume or skip the returned [`RubyType`] before retrieving the next one.
    ///
    /// Consumes and returns the next pair of elements as a 2-tuple of [`RubyType`]s.
    ///
    /// Returns `Some((key, value))` if a tuple was deserialized, or `None` if the
    /// iterator has been fully exhausted.
    #[deprecated(
        since = "0.1.1",
        note = "this method is misleading and cannot be fixed, and it will be removed
        on the next minor release. Use `RubyMapIter::next_element` instead, ensuring
        you fully consume or skip the returned `RubyType` before retrieving the next one."
    )]
    pub fn next<'de>(
        &mut self,
        deserializer: &mut Deserializer<'de>,
    ) -> Result<Option<(RawRubyType<'de>, RawRubyType<'de>)>> {
        if self.current_index >= self.num_elements() {
            return Ok(None);
        }

        let a = deserializer.next_raw_element()?;
        let b = deserializer.next_raw_element()?;
        self.current_index += 2;
        Ok(Some((a, b)))
    }

    /// Consumes and returns the next pair of elements as a 2-tuple of the specified types.
    ///
    /// **This method is provided as convenience.** If reducing code size bloat is desired,
    /// it is advised to instead use a pair of [`RubyMapIter::next_element_of_type()`] calls.
    ///
    /// Returns `Some((key, value))` if a tuple was deserialized, or `None` if the
    /// iterator has been fully exhausted.
    pub fn next_of_type<'de, T, U>(
        &mut self,
        deserializer: &mut Deserializer<'de>,
    ) -> Result<Option<(T, U)>>
    where
        T: FromRubyMarshal<'de>,
        U: FromRubyMarshal<'de>,
    {
        if self.current_index >= self.num_elements() {
            return Ok(None);
        }

        let a = T::deserialize(deserializer)?;
        let b = U::deserialize(deserializer)?;
        self.current_index += 2;
        Ok(Some((a, b)))
    }

    /// Consumes and returns the next element as a `T` implementing [`FromRubyMarshal`].
    ///
    /// **This does not keep track of whether the returned element is a key or a value.**
    /// Callers must ensure to call this method in pairs.
    ///
    /// Returns `Some(data)` if a tuple was deserialized, or `None` if the iterator has
    /// been fully exhausted.
    pub fn next_element<'de>(
        &mut self,
        deserializer: &mut Deserializer<'de>,
    ) -> Result<Option<RawRubyType<'de>>> {
        if self.current_index >= self.num_elements() {
            return Ok(None);
        }

        let next = deserializer.next_raw_element()?;
        self.current_index += 1;
        Ok(Some(next))
    }

    /// Consumes and returns the next element as a [`RawRubyType`].
    ///
    /// **This does not keep track of whether the returned element is a key or a value.**
    /// Callers must ensure to call this method in pairs.
    ///
    /// Returns `Some(data)` if a tuple was deserialized, or `None` if the iterator has
    /// been fully exhausted.
    pub fn next_element_of_type<'de, T: FromRubyMarshal<'de>>(
        &mut self,
        deserializer: &mut Deserializer<'de>,
    ) -> Result<Option<T>> {
        if self.current_index >= self.num_elements() {
            return Ok(None);
        }

        let next = T::deserialize(deserializer)?;
        self.current_index += 1;
        Ok(Some(next))
    }

    /// Skips the remaining elements of the map.
    ///
    /// This can be more efficent than calling [`RubyArrayIter::next()`]/[`RubyArrayIter::next_of_type()`].
    pub fn skip(mut self, deserializer: &mut Deserializer) -> Result<()> {
        self.skip_impl(deserializer)
    }

    fn skip_impl(&mut self, deserializer: &mut Deserializer) -> Result<()> {
        let num_elements = self.num_elements();
        if self.current_index >= num_elements {
            return Ok(());
        }
        while self.current_index < num_elements {
            deserializer.skip_element()?;
            self.current_index += 1;
        }
        Ok(())
    }

    /// Returns the total number of element pairs in the map.
    pub fn size_hint_pairs(&self) -> usize {
        self.num_pairs
    }

    fn num_elements(&self) -> usize {
        self.num_pairs * 2
    }
}

/// A lending iterator over the elements of a Ruby hash.
///
/// **IMPORTANT: You must either fully consume or skip this iterator before dropping it;
/// the deserializer does not track how far into the map it has has advanced.**
pub struct RubyMapIter<'de, 'deser> {
    inner: RawRubyMapIter,
    deserializer: &'deser mut Deserializer<'de>,
}

impl<'de, 'deser> RubyMapIter<'de, 'deser> {
    pub fn from_raw(raw: RawRubyMapIter, deserializer: &'deser mut Deserializer<'de>) -> Self {
        Self {
            inner: raw,
            deserializer,
        }
    }

    /// Consumes and returns the next pair of elements as a 2-tuple of the specified types.
    ///
    /// **This method is provided as convenience.** If reducing code size bloat is desired,
    /// it is advised to instead use a pair of [`RubyMapIter::next_element_of_type()`] calls.
    ///
    /// Returns `Some((key, value))` if a tuple was deserialized, or `None` if the
    /// iterator has been fully exhausted.
    pub fn next_of_type<T, U>(&mut self) -> Result<Option<(T, U)>>
    where
        T: FromRubyMarshal<'de>,
        U: FromRubyMarshal<'de>,
    {
        if self.inner.current_index >= self.num_elements() {
            return Ok(None);
        }

        let a = T::deserialize(self.deserializer)?;
        let b = U::deserialize(self.deserializer)?;
        self.inner.current_index += 2;
        Ok(Some((a, b)))
    }

    /// Consumes and returns the next element as a `T` implementing [`FromRubyMarshal`].
    ///
    /// **This does not keep track of whether the returned element is a key or a value.**
    /// Callers must ensure to call this method in pairs.
    ///
    /// Returns `Some(data)` if a tuple was deserialized, or `None` if the iterator has
    /// been fully exhausted.
    pub fn next_element<'deser_new>(
        &'deser_new mut self,
    ) -> Result<Option<RubyTypeGuard<'de, 'deser_new>>> {
        if self.inner.current_index >= self.num_elements() {
            return Ok(None);
        }

        let next = self.deserializer.next_element()?;
        self.inner.current_index += 1;
        Ok(Some(next))
    }

    pub fn next_raw_element(&mut self) -> Result<Option<RawRubyType>> {
        self.inner.next_element(self.deserializer)
    }

    pub fn skip_element(&mut self) -> Result<Option<()>> {
        if self.inner.current_index >= self.num_elements() {
            return Ok(None);
        }

        self.deserializer.skip_element()?;
        self.inner.current_index += 1;
        Ok(Some(()))
    }

    /// Consumes and returns the next element as a [`RubyType`].
    ///
    /// **This does not keep track of whether the returned element is a key or a value.**
    /// Callers must ensure to call this method in pairs.
    ///
    /// Returns `Some(data)` if a tuple was deserialized, or `None` if the iterator has
    /// been fully exhausted.
    pub fn next_element_of_type<T: FromRubyMarshal<'de>>(&mut self) -> Result<Option<T>> {
        if self.inner.current_index >= self.num_elements() {
            return Ok(None);
        }

        let next = T::deserialize(self.deserializer)?;
        self.inner.current_index += 1;
        Ok(Some(next))
    }

    /// Skips the remaining elements of the map.
    ///
    /// This can be more efficent than calling [`RubyArrayIter::next()`]/[`RubyArrayIter::next_of_type()`].
    pub fn skip(mut self) -> Result<()> {
        self.inner.skip_impl(self.deserializer)
    }

    /// Returns the total number of element pairs in the map.
    pub fn size_hint_pairs(&self) -> usize {
        self.inner.size_hint_pairs()
    }

    fn num_elements(&self) -> usize {
        self.inner.num_elements()
    }
}

impl<'de: 'deser, 'deser> Drop for RubyMapIter<'de, 'deser> {
    fn drop(&mut self) {
        self.inner.skip_impl(self.deserializer);
    }
}

#[derive(Clone)]
pub struct RawRubyIvar {
    _private: PhantomData<()>,
}

impl RawRubyIvar {
    /// Reads the underlying boxed data into a [`RubyType`].
    ///
    /// Consumes this `RubyIvar` and returns the read data as a [`RubyType`] and a
    /// [`RubyMapIter`] over the instance variables.
    pub fn read_data<'de>(
        self,
        deserializer: &mut Deserializer<'de>,
    ) -> Result<(RawRubyType<'de>, RawRubyMapIter)> {
        deserializer.add_current_position_as_blacklisted();
        let data = deserializer.next_raw_element()?;
        deserializer.add_current_position_as_blacklisted();
        let map = deserializer.read_hash()?;
        Ok((data, map))
    }

    /// Skips the underlying boxed data.
    ///
    /// Consumes this `RubyIvar` and returns a [`RubyMapIter`] over the instance variables.
    pub fn skip_data(self, deserializer: &mut Deserializer) -> Result<RawRubyMapIter> {
        deserializer.add_current_position_as_blacklisted();
        deserializer.skip_element()?;
        deserializer.add_current_position_as_blacklisted();
        let map = deserializer.read_hash()?;
        Ok(map)
    }

    /// Reads the underlying boxed data into a `T` implementing [`FromRubyMarshal`].
    ///
    /// Consumes this `RubyIvar` and returns the read data as a instance of `T` and a
    /// [`RubyMapIter`] over the instance variables.
    pub fn read_data_of_type<'de, T: FromRubyMarshal<'de>>(
        self,
        deserializer: &mut Deserializer<'de>,
    ) -> Result<(T, RawRubyMapIter)> {
        deserializer.add_current_position_as_blacklisted();
        let data = T::deserialize(deserializer)?;
        deserializer.add_current_position_as_blacklisted();
        let map = deserializer.read_hash()?;
        Ok((data, map))
    }

    /// Skips the entire IVAR object, including instance variables.
    pub fn skip(self, deserializer: &mut Deserializer) -> Result<()> {
        Self::skip_impl(deserializer)
    }

    fn skip_impl(deserializer: &mut Deserializer) -> Result<()> {
        deserializer.add_current_position_as_blacklisted();
        deserializer.skip_element()?;
        deserializer.add_current_position_as_blacklisted();
        let map = deserializer.read_hash()?;
        map.skip(deserializer)
    }
}

/// A structure that provides access to a Ruby IVAR (instance variable) object.
///
/// IVAR objects, in the Marshal data model, are containers over data that also provide
/// additional metadata in the form of a key-value store; the elements on the latter are
/// called "instance variables". Conceptually, they can be described as a boxed value
/// with a map attached.
///
/// Within the Marshal data model, IVAR objects are used to encode, among other things:
///
/// - **Ruby strings**, where the boxed data is the raw byte representation of the string and the
///   instance variables describe the string encoding.
/// - **Ruby regular expressions**, where the boxed data is a raw byte representation of the
///   regular expression and its flags (see [`RubyRegexp`]) and the instance variables describe
///   the string encoding of the regular expression itself.
/// - **Objects with user-defined deserialization logic**.
///
/// # Reading from IVAR objects
///
/// To process an IVAR object, it is first required to process the underlying boxed data.
/// To do so, you may read it using one of the following:
///    - [`RubyIvar::read_data()`], which returns a [`RubyType`], or
///    - [`RubyIvar::read_data_of_type()`], which delegates deserialization to a provided
///      `T: FromRubyMarshal`.
///
/// Both of these options consume the `RubyIvar` and return a [`RubyMapIter`] that allows
/// processing of the instance variables.
///
/// You may also skip the entire IVAR object, including instance variables, using [`RubyIvar::skip()`].
///
/// **IMPORTANT: You must either fully consume or skip the `RubyIvar` before dropping it;
/// the deserializer does not track how far into the IVAR object it has has advanced.**
///
/// **The same applies to the returned [`RubyMapIter`] containing the instance variables.**
///
/// It is to be noted, though, that the handling of the [`RubyMapIter`] is independent:
/// one may choose to read the boxed data and skip the instance variables, for example.
pub struct RubyIvar<'de: 'deser, 'deser> {
    inner: RawRubyIvar,
    deserializer: &'deser mut Deserializer<'de>,
}

/// A [`RubyIvar`] with no destructor.
///
/// Used internally to "defuse" [`RubyIvar`]'s `Drop` implementation.
struct RubyIvarFields<'de: 'deser, 'deser> {
    _inner: RawRubyIvar,
    deserializer: &'deser mut Deserializer<'de>,
}

impl<'de: 'deser, 'deser> RubyIvar<'de, 'deser> {
    pub fn from_raw(raw: RawRubyIvar, deserializer: &'deser mut Deserializer<'de>) -> Self {
        Self {
            inner: raw,
            deserializer,
        }
    }

    unsafe fn defuse_drop(self) -> RubyIvarFields<'de, 'deser> {
        use std::{mem::MaybeUninit, ptr};

        // We are going to uninitialize the value.
        let x = MaybeUninit::new(self);

        // Deliberately shadow the value so we can't even try to drop it.
        let x = x.as_ptr();

        // SAFETY: All fields are read; therefore no memory is leaked.
        let inner = ptr::read(&(*x).inner);
        let deserializer = ptr::read(&(*x).deserializer);

        RubyIvarFields {
            _inner: inner,
            deserializer,
        }
    }

    /// Skips the underlying boxed data.
    ///
    /// Consumes this `RubyIvar` and returns a [`RubyMapIter`] over the instance variables.
    pub fn skip_data(self) -> Result<RubyMapIter<'de, 'deser>> {
        self.deserializer.add_current_position_as_blacklisted();
        self.deserializer.skip_element()?;
        self.deserializer.add_current_position_as_blacklisted();
        let map = self.deserializer.read_hash()?;

        // SAFETY: we have read everything successfully, therefore it is safe
        // to skip the destructor
        let RubyIvarFields {
            _inner: _,
            deserializer,
        } = unsafe { self.defuse_drop() };
        Ok(RubyMapIter::from_raw(map, deserializer))
    }

    /// Reads the underlying boxed data into a `T` implementing [`FromRubyMarshal`].
    ///
    /// Consumes this `RubyIvar` and returns the read data as a instance of `T` and a
    /// [`RubyMapIter`] over the instance variables.
    pub fn read_data_of_type<T: FromRubyMarshal<'de>>(
        self,
    ) -> Result<(T, RubyMapIter<'de, 'deser>)> {
        self.deserializer.add_current_position_as_blacklisted();
        let data = T::deserialize(self.deserializer)?;
        self.deserializer.add_current_position_as_blacklisted();
        let map = self.deserializer.read_hash()?;
        let RubyIvarFields {
            _inner: _,
            deserializer,
        } = unsafe { self.defuse_drop() };
        Ok((data, RubyMapIter::from_raw(map, deserializer)))
    }

    /// Skips the entire IVAR object, including instance variables.
    pub fn skip(self) -> Result<()> {
        RawRubyIvar::skip_impl(self.deserializer)
    }
}

#[derive(Clone)]
/// A raw Ruby regular expression.
///
/// Similar to [`RubyType::ByteArray`], but also contains the regular expression's flags.
pub struct RubyRegexp<'de> {
    /// The regular expression's contents as a raw byte array.
    ///
    /// This would be the part of the regular expression that goes `/here/`.
    ///
    /// The encoding of this byte array **cannot be assumed**. `RubyRegexp`s almost always
    /// come as a boxed object of a [`RubyIvar`] where the instance variables provide
    /// the encoding.
    pub expr: &'de [u8],

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

impl<'de> FromRubyMarshal<'de> for RubyRegexp<'de> {
    fn deserialize(deserializer: &mut Deserializer<'de>) -> Result<Self> {
        match deserializer.next_element()?.get() {
            RubyType::RawRegexp(regexp) => Ok(regexp),
            _ => Err(ParsingError::Message("expected raw regexp".to_string())),
        }
    }
}

#[derive(Clone)]
pub struct RawRubyObject<'de> {
    class_name: &'de str,
    fields: RawRubyMapIter,
}

impl<'de> RawRubyObject<'de> {
    pub fn skip(self, deserializer: &mut Deserializer) -> Result<()> {
        self.fields.skip(deserializer)
    }
}

/// A Ruby object.
///
/// This is different from a Ruby IVAR object ([`RubyIvar`]) in that the boxed value
/// is always a symbol containing the name of the instanced class.
/// The deserializer parses this class name eagerly, and as such the class properties
/// are immediately provided as a [`RubyMapIter`].
///
/// To handle a `RubyObject`, either **fully consume or skip** the provided
/// [`RubyMapIter#fields`]. If skipping is desired, you may use the convenience
/// method [`RubyMapIter::skip()`].
pub struct RubyObject<'de: 'deser, 'deser> {
    /// The name of the class from which this object was instanced.
    pub class_name: &'de str,

    /// A lending iterator over the object's properties.
    pub fields: RubyMapIter<'de, 'deser>,
}

impl<'de: 'deser, 'deser> RubyObject<'de, 'deser> {
    pub fn from_raw(raw: RawRubyObject<'de>, deserializer: &'deser mut Deserializer<'de>) -> Self {
        Self {
            class_name: raw.class_name,
            fields: RubyMapIter::from_raw(raw.fields, deserializer),
        }
    }

    /// Convenience method for `self.fields.skip`.
    pub fn skip(self) -> Result<()> {
        self.fields.skip()
    }
}

#[derive(Clone)]
/// User-defined marshalling data from a Ruby class with a `_dump` method.
pub struct RubyUserDef<'de> {
    /// The name of the class from which this object was instanced.
    pub class_name: &'de str,

    /// The raw data returned from the Ruby class's `_dump` method.
    pub data: &'de [u8],
}

#[cfg(test)]
mod tests {
    #[allow(clippy::cast_lossless)]
    mod packed_integer {
        use crate::de::{MAX_MARSHAL_INTEGER, MIN_MARSHAL_INTEGER};

        use super::super::{Deserializer, FromRubyMarshal, Result};

        fn read_ruby_packed_integer(input: &[u8]) -> Result<i32> {
            let mut input_with_prelude: Vec<u8> = vec![0x04, 0x08, b'i'];
            input_with_prelude.extend_from_slice(input);
            let mut deserializer = Deserializer::from_bytes(&input_with_prelude);
            i32::deserialize(&mut deserializer)
        }

        #[test]
        fn zero() {
            let input: &[u8] = &[0x00];
            let expected = 0;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn positive_small_integers() {
            for expected in 1i8..122 {
                let input: &[u8] = &[0x05 + expected.unsigned_abs()];

                let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

                assert_eq!(deserialized, expected as i32);
            }
        }

        #[test]
        fn negative_small_integers() {
            for expected in -123i8..-1 {
                let input: &[u8] = &[0xfb - expected.unsigned_abs()];

                let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

                assert_eq!(deserialized, expected as i32);
            }
        }

        #[test]
        fn positive_inner_boundary() {
            let input: &[u8] = &[0x7f];
            let expected = 122;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn positive_outer_boundary() {
            let input: &[u8] = &[0x01, 0x7b];
            let expected = 123;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn negative_inner_boundary() {
            let input: &[u8] = &[0x80];
            let expected = -123;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn negative_outer_boundary() {
            let input: &[u8] = &[0xff, 0x84];
            let expected = -124;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn b2_positive_inner_boundary() {
            let input: &[u8] = &[0x01, 0xff];
            let expected = 255;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn b2_positive_outer_boundary() {
            let input: &[u8] = &[0x02, 0x00, 0x01];
            let expected = 256;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn b2_negative_inner_boundary() {
            let input: &[u8] = &[0xff, 0x00];
            let expected = -256;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn b2_negative_outer_boundary() {
            let input: &[u8] = &[0xfe, 0xff, 0xfe];
            let expected = -257;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn b3_positive_inner_boundary() {
            let input: &[u8] = &[0x02, 0xff, 0xff];
            let expected = 65535;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn b3_positive_outer_boundary() {
            let input: &[u8] = &[0x03, 0x00, 0x00, 0x01];
            let expected = 65536;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn b3_negative_inner_boundary() {
            let input: &[u8] = &[0xfe, 0x00, 0x00];
            let expected = -65536;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn b3_negative_outer_boundary() {
            let input: &[u8] = &[0xfd, 0xff, 0xff, 0xfe];
            let expected = -65537;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn b4_positive_inner_boundary() {
            let input: &[u8] = &[0x03, 0xff, 0xff, 0xff];
            let expected = 0x00FF_FFFF_i32;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn b4_positive_outer_boundary() {
            let input: &[u8] = &[0x04, 0x00, 0x00, 0x00, 0x01];
            let expected = 0x0100_0000_i32;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn b4_negative_inner_boundary() {
            let input: &[u8] = &[0xfd, 0x00, 0x00, 0x00];
            let expected = -16_777_216;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn b4_negative_outer_boundary() {
            let input: &[u8] = &[0xfc, 0xff, 0xff, 0xff, 0xfe];
            let expected = -16_777_217;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn max_value() {
            let input: &[u8] = &[0x04, 0xff, 0xff, 0xff, 0x3f];
            let expected = MAX_MARSHAL_INTEGER;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }

        #[test]
        fn min_value() {
            let input: &[u8] = &[0xfc, 0x00, 0x00, 0x00, 0xc0];
            let expected = MIN_MARSHAL_INTEGER;

            let deserialized = read_ruby_packed_integer(input).expect("Not successful!");

            assert_eq!(deserialized, expected);
        }
    }
}
