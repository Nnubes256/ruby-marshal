use std::{
    fmt::Debug,
    fs::{self, File},
    io::{self, Write},
    path::PathBuf,
    sync::RwLock,
};

use ruby_marshal::{
    de::{FromRubyMarshal, ParsingError},
    value::{ValueHL, ValueLL},
};

/// Ensures reads and writes to "expected output" files do not
/// produce odd race conditions due to test parallelism.
static EXPECTED_FILE_OPERATIONS_LOCK: RwLock<()> = RwLock::new(());

/// A trait to fetch the type name of a type.
///
/// This is used to put it on the "expected" file's name for identification
/// and uniqueness.
trait TypeName {
    fn type_name() -> &'static str;
}

/// Macro to implement [TypeName] without hassle.
macro_rules! impl_typename {
    ($ty:ty) => {
        impl TypeName for $ty {
            fn type_name() -> &'static str {
                stringify!($ty)
            }
        }
    };
}

impl_typename!(ValueHL);
impl_typename!(ValueLL);

fn resolve_test_vector_file(bin_path: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("test-vectors")
        .join(bin_path)
}

fn should_pass<T>(bin_path: &str)
where
    T: for<'de> FromRubyMarshal<'de> + TypeName + Debug,
{
    let bin_path = resolve_test_vector_file(bin_path);
    let expected_path = bin_path.with_extension(format!("expected-{}.txt", T::type_name()));
    eprint!(
        "Testing {} ... ",
        bin_path.file_stem().unwrap().to_string_lossy()
    );
    let input = fs::read(bin_path).expect("failed to read file");

    // PARSING HAPPENS HERE
    let output: T = ruby_marshal::from_bytes(&input).expect("parsing failed");

    let read_lock = EXPECTED_FILE_OPERATIONS_LOCK.read().unwrap();
    let read_result = fs::read(&expected_path);
    drop(read_lock);

    match read_result {
        Ok(expected_data) => {
            let expected_data = String::from_utf8(expected_data).unwrap_or_else(|_| {
                panic!(
                    "Expected file is no longer valid UTF-8: {}",
                    expected_path.display()
                )
            });
            let got_data = format!("{:#?}", output);
            if got_data.trim() == expected_data.trim() {
                eprintln!("ok!");
            } else {
                eprintln!("MISMATCH!");
                eprintln!("\nEXPECTED:\n{expected_data}\nGOT:\n{got_data}");
                panic!("mismatch!");
            }
        }
        Err(err) if err.kind() == io::ErrorKind::NotFound => {
            eprintln!("NEW!");

            let write_lock = EXPECTED_FILE_OPERATIONS_LOCK.write().unwrap();
            let mut file = File::options()
                .read(true)
                .write(true)
                .create_new(true)
                .open(&expected_path)
                .expect("failed to create file");
            write!(file, "{:#?}", output).expect("failed to write expected result");
            drop(write_lock);

            eprintln!(
                "    {}: expected output didn't exist, it has now been written, check for errors before commiting",
                expected_path.display()
            );
        }
        Err(err) => panic!("{}", err), // :V
    }
}

fn should_fail<T>(bin_path: &str, expected_error: &ParsingError)
where
    T: for<'de> FromRubyMarshal<'de> + TypeName + Debug,
{
    let bin_path = resolve_test_vector_file(bin_path);
    eprint!(
        "Testing {} ... ",
        bin_path.file_stem().unwrap().to_string_lossy()
    );
    let input = fs::read(bin_path).expect("failed to read file");

    let output: ParsingError = ruby_marshal::from_bytes::<T>(&input)
        .expect_err("parsing actually succeeded; that shouldn't happen!");

    assert_eq!(output, *expected_error);
}

fn should_pass_value(bin_path: &str) {
    should_pass::<ValueLL>(bin_path);
    should_pass::<ValueHL>(bin_path);
}

fn should_fail_value(bin_path: &str, expected_error: &ParsingError) {
    should_fail::<ValueLL>(bin_path, expected_error);
    should_fail::<ValueHL>(bin_path, expected_error);
}

#[test]
fn object_links_object() {
    should_pass_value("object_links_object.bin");
}

#[test]
fn object_links_nested() {
    should_pass_value("object_links_nested.bin");
}

#[test]
fn types_playground() {
    should_pass_value("types_playground.bin");
}

#[test]
fn stack_depth_limit_array() {
    should_fail_value(
        "stack_depth_limit_array.bin",
        &ParsingError::StackDepthLimitExceeded,
    )
}

#[test]
fn recursion_limit_array() {
    should_fail_value(
        "recursion_limit_array.bin",
        &ParsingError::RecursionLimitExceeded,
    )
}
