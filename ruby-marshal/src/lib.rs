//! A deserialization library for Ruby's marshalling format.
//!
//! # ⚠️ WARNING ⚠️
//!
//! **This crate is *really* experimental. Not intended for production applications.**
//!
//! It does not support the entiretly of Ruby Marshal (yet), it contains a bunch of **footguns**,
//! testing coverage is not really the best and, overall, this crate is Serde but worse.
//! One could call it "bootleg homebrew Serde for Ruby Marshal".
//!
//! This was ultimately intended to be a learning/experimentation project that ultimately got
//! a bit overblown. **Use at your own risk!**
//!
//! # Getting started
//!
//! If you want to get deserializing right away, make sure your target Rust types implement
//! [`FromRubyMarshal`] and  use the convenience method [`from_bytes`] to get started.
//!
//! For simple cases can use the provided [derive macro](derive@FromRubyMarshal) to quickly implement [`FromRubyMarshal`]
//! on your types:
//!
//! ```
//! use ruby_marshal::{self, FromRubyMarshal};
//!
//! #[derive(Debug, FromRubyMarshal)]
//! struct Test {
//!     thing1: i32,
//!     thing2: Option<String>,
//!     thing3: Vec<i32>,
//! }
//!
//! // ruby: Marshal.dump({:thing1 => 1, :thing2 => "hello", :thing3 => [1,2,3]})
//! let input: &[u8] = &[
//!     0x04, 0x08, 0x7b, 0x08, 0x3a, 0x0b, 0x74, 0x68, 0x69, 0x6e, 0x67,
//!     // ...
//! #    0x31, 0x69, 0x06, 0x3a,
//! #    0x0b, 0x74, 0x68, 0x69, 0x6e, 0x67, 0x32, 0x49, 0x22, 0x0a, 0x68, 0x65, 0x6c, 0x6c, 0x6f,
//! #    0x06, 0x3a, 0x0d, 0x65, 0x6e, 0x63, 0x6f, 0x64, 0x69, 0x6e, 0x67, 0x22, 0x0e, 0x53, 0x68,
//! #    0x69, 0x66, 0x74, 0x5f, 0x4a, 0x49, 0x53, 0x3a, 0x0b, 0x74, 0x68, 0x69, 0x6e, 0x67, 0x33,
//! #    0x5b, 0x08, 0x69, 0x06, 0x69, 0x07, 0x69, 0x08,
//! ];
//! let out = ruby_marshal::from_bytes::<Test>(input).expect("parsing failed");
//! assert_eq!(out.thing1, 1);
//! assert_eq!(out.thing2, Some("hello".to_string()));
//! assert_eq!(out.thing3, vec![1, 2, 3]);
//! ```
//!
//! [`FromRubyMarshal`] can also be implemented manually.
//!
//! # Features
//!
//! - Deserialize binary Ruby Marshal objects into:
//!     - Rust values that implement [`FromRubyMarshal`].
//!     - [Arbitrary value types](value).
//! - A [derive macro](derive@FromRubyMarshal) to automatically implement [`FromRubyMarshal`], Serde style.
//!     - Allows deserialization of named `struct`s (e.g. `Point { x: 1, y: 2 }`) from Ruby hashes and
//!       IVAR objects (normal objects soon to follow).
//!     - Field renaming support.
//!     - Borrowed data support on types that use the `'de` lifetime.
//!
//! # Roadmap
//!
//! - [ ] Full Ruby Marshal 4.8 support:
//!     - [x] `nil`
//!     - [x] Booleans (`true`, `false`).
//!     - [x] Integers (`0`, `320`).
//!     - [x] Floating-point numbers (`0.2`, `Math::PI`).
//!     - [x] Symbols (`:foo`), with support for resolving symlinks.
//!     - [x] Arrays (`[1, 2, 3]`).
//!     - [x] Hashes (`{:a => 1, :b => 2}`).
//!     - [x] Byte arrays.
//!     - [x] IVAR-wrapped objects.
//!         - [x] Strings with encoding.
//!         - [x] Regular expressions (**not yet stable**).
//!     - [x] Class and module references.
//!     - [x] Objects, with support for resolving object links.
//!     - [ ] Bignums (numbers outside of the [-2<sup>30</sup>, 2<sup>30</sup> - 1] range).
//!     - [ ] Custom marshalled objects:
//!         - [x] `_dump`, `_load`
//!         - [ ] `marshal_dump`, `marshal_load`
//!     - [ ] Additional low-level format tags:
//!         - [ ] `TYPE_EXTENDED` (`e`)
//!         - [ ] `TYPE_UCLASS` (`C`)
//!         - [ ] `TYPE_DATA` (`d`)
//!         - [ ] `TYPE_USRMARSHAL` (`U`)
//!         - [ ] `TYPE_HASH_DEF` (`}`)
//!         - [ ] `TYPE_MODULE_OLD` (`M`)
//! - [ ] A derive macro that doesn't suck.
//!     - [ ] Rust type system support.
//!         - [x] Named structures (`struct Point { x: 1, y: 2 }`).
//!         - [ ] Enums (`enum Variant { A, B }`).
//!         - [x] Borrowed data support (`<'de>`).
//!         - [ ] Generics (`struct Container<T: FromRubyMarshal> { /* ... */ }`).
//!     - [ ] Rust types support.
//!         - Any user type that implements [`FromRubyMarshal`].
//!         - [x] `bool`
//!         - [x] Unsigned integers: `u8`, `u16`, `u32`, `u64`, `u128`, `usize`.
//!         - [x] Signed integers: `i8`, `i16`, `i32`, `i64`, `i128`, `isize`.
//!         - [x] Floating-point numbers: `f32`, `f64`.
//!         - [x] Borrowed byte slices: `&'de [u8]`.
//!         - [x] `String`, `Cow<'de, str>`.
//!         - [x] `Box<T>`.
//!         - [x] `Option<T>`.
//!         - [x] `Vec<T>` (arrays), `Vec<(T, U)> (hashes)`.
//!         - [x] `HashMap<K, V>`
//!             - Requires `K: Eq + Hash`.
//!             - Any `BuildHasher` that implements `Default` is supported.
//!         - [x] `BTreeMap<K, V>`
//!             - Requires `K: Ord`.
//!         - [ ] ...some other types not yet considered...
//!     - [ ] Marshal format support.
//!         - [x] Hashes (`{:a => 1, :b => 2}`).
//!         - [x] IVAR objects.
//!         - [ ] Objects.
//!     - [x] Annotation-based functionality.
//!         - [x] Field renaming (`#[marshal(rename = "foo")`).
//!         - [x] Selecting where to deserialize the boxed data of an IVAR object (`#[marshal(ivar_data)]`).
//!         - [ ] Pluggable logic to deserialize from custom marshalled objects.
//!         - ...etc...
//!

#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::nursery)]
#![warn(missing_docs)]
#![allow(clippy::missing_errors_doc)]
#![allow(clippy::items_after_statements)]
#![allow(
    clippy::module_name_repetitions,
    clippy::must_use_candidate,
    clippy::missing_const_for_fn,
    clippy::inefficient_to_string,
    clippy::multiple_crate_versions,
    clippy::redundant_pub_crate,
    clippy::use_self
)]
extern crate alloc;

use de::{DeserializerOptions, ParsingError};

pub mod de;
pub mod value;

#[doc(inline)]
pub use de::Deserializer;
#[doc(inline)]
pub use de::FromRubyMarshal;

/// Automatically implement [`FromRubyMarshal`].
///
/// # Deserializing a Ruby hash
///
/// By default, applying `#[derive(FromRubyMarshal)]` on a named `struct` generates
/// code to deserialize a Ruby hash (i.e. `{:a => 1, :b => 2}`).
///
/// The derive macro uses the name of the field in Rust to identify which **symbol** key
/// of the Ruby hash to deserialize. This can be overriden for each field by annotating
/// it with the `#[marshal(rename = "foobar")]` annotation, which will cause the
/// deserializer to look for a field with key `:foobar`.
///
/// ```
/// use ruby_marshal::{self, FromRubyMarshal};
///
/// #[derive(Debug, FromRubyMarshal)]
/// struct Test {
///     thing1: i32,
///     thing2: Option<String>,
///     #[marshal(rename = "thing3")]
///     extra_data: Vec<i32>,
/// }
///
/// // ruby: Marshal.dump({:thing1 => 1, :thing2 => "hello", :thing3 => [1,2,3]})
/// let input: &[u8] = &[
///     0x04, 0x08, 0x7b, 0x08, 0x3a, 0x0b, 0x74, 0x68, 0x69, 0x6e, 0x67, // ...
/// #    0x31, 0x69, 0x06, 0x3a,
/// #    0x0b, 0x74, 0x68, 0x69, 0x6e, 0x67, 0x32, 0x49, 0x22, 0x0a, 0x68, 0x65, 0x6c, 0x6c, 0x6f,
/// #    0x06, 0x3a, 0x0d, 0x65, 0x6e, 0x63, 0x6f, 0x64, 0x69, 0x6e, 0x67, 0x22, 0x0e, 0x53, 0x68,
/// #    0x69, 0x66, 0x74, 0x5f, 0x4a, 0x49, 0x53, 0x3a, 0x0b, 0x74, 0x68, 0x69, 0x6e, 0x67, 0x33,
/// #    0x5b, 0x08, 0x69, 0x06, 0x69, 0x07, 0x69, 0x08,
/// ];
/// let out = ruby_marshal::from_bytes::<Test>(input).expect("parsing failed");
/// assert_eq!(out.thing1, 1);
/// assert_eq!(out.thing2, Some("hello".to_string()));
/// assert_eq!(out.extra_data, vec![1, 2, 3]);
/// ```
///
/// # Deserializing an IVAR object
///
/// IVAR objects can be deserialized by annotating one of the fields with `#[marshal(ruby_data)]`.
/// The annotated field will received the IVAR object's boxed data, and the rest of the fields will
/// receive the IVAR object's instance variables as with a Ruby hash.
///
/// ```
/// // An example where we deserialize a Ruby string.
/// // Ruby strings on the Marshal data format are encoded as IVARs where the boxed data
/// // is a raw byte array with the string data, and its encoding is provided in the
/// // instance variables.
/// //
/// // This example also demonstrates how to perform zero-copy deserialization of certain fields;
/// // all that's required is to annotate such fields with the `'de` lifetime.
///
/// use ruby_marshal::{self, FromRubyMarshal};
///
/// #[derive(FromRubyMarshal)]
/// struct StringRaw<'de> {
///     #[marshal(ivar_data)]
///     data: &'de [u8],
///     #[marshal(rename = "E")]
///     encoding_short: Option<bool>,
///     encoding: Option<&'de [u8]>,
/// }
///
/// // ruby: Marshal.dump("hello")
/// let input: &[u8] = &[
///     0x04, 0x08,                                // marshal header
///     b'I',                                      // IVAR object start
///     b'"', 0x0a, b'h', b'e', b'l', b'l', b'o',  // boxed data: b"hello"
///     0x06, b':', 0x06, b'E', b'T'               // instance variables: {:E => true}
/// ];
/// let out = ruby_marshal::from_bytes::<StringRaw<'_>>(input).expect("parsing failed");
/// assert_eq!(out.data, &[b'h', b'e', b'l', b'l', b'o']);
/// assert_eq!(out.encoding, None);
/// assert_eq!(out.encoding_short, Some(true));
/// ```
pub use ruby_marshal_derive::FromRubyMarshal;

/// Deserializes a binary Marhsal object into a given `T`.
///
/// # Errors
///
/// Besides the errors that may be returned through deserializing, this function
/// checks if the output was fully consumed; if it was not, a
/// [`ParsingError::TrailingData`] will be returned. If this behavior is not desired,
/// it is possible to instantiate the [`Deserializer`] directly;
/// see [`Deserializer::from_bytes()`].
///
/// # Example
/// ```
/// let input = [0x04, 0x08, b'T']; // Marshal.dump(true)
/// let output: Result<bool, _> = ruby_marshal::from_bytes(&input);
/// assert_eq!(output, Ok(true));
/// ```
pub fn from_bytes<'de, T>(input: &'de [u8]) -> de::Result<T>
where
    T: de::FromRubyMarshal<'de>,
{
    let mut deserializer = Deserializer::from_bytes(input);
    let t = T::deserialize(&mut deserializer)?;
    if deserializer.input.is_empty() {
        Ok(t)
    } else {
        Err(ParsingError::TrailingData)
    }
}

/// Deserializes a binary Marhsal object into a given `T` providing additional settings.
///
/// # Errors
///
/// Besides the errors that may be returned through deserializing, this function
/// checks if the output was fully consumed; if it was not, a
/// [`ParsingError::TrailingData`] will be returned. If this behavior is not desired,
/// it is possible to instantiate the [`Deserializer`] directly;
/// see [`Deserializer::from_bytes_with_options()`].
///
/// # Example
/// ```
/// # use ruby_marshal::de::{DeserializerOptions, ParsingError};
/// use ruby_marshal::value::ValueHL;
///
/// // Marshal.dump([[[[]]]])
/// let input = [0x04, 0x08, b'[', 0x06, b'[', 0x06, b'[', 0x06, b'[', 0x00];
///
/// let output: Result<ValueHL, _> = ruby_marshal::from_bytes_with_options(
///     &input,
///     &Default::default()
/// );
/// assert!(output.is_ok());
///
/// let output: Result<ValueHL, ParsingError> = ruby_marshal::from_bytes_with_options(
///     &input,
///     &DeserializerOptions {
///         recursion_limit: 2,
///         ..Default::default()
///     }
/// );
/// assert_eq!(output, Err(ParsingError::RecursionLimitExceeded));
/// ```
pub fn from_bytes_with_options<'de, T>(
    input: &'de [u8],
    options: &DeserializerOptions,
) -> de::Result<T>
where
    T: de::FromRubyMarshal<'de>,
{
    let mut deserializer = Deserializer::from_bytes_with_options(input, options);
    let t = T::deserialize(&mut deserializer)?;
    if deserializer.input.is_empty() {
        Ok(t)
    } else {
        Err(ParsingError::TrailingData)
    }
}
