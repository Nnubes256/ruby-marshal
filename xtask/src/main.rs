#![allow(clippy::cargo)]

use std::{
    env,
    error::Error,
    ffi::OsStr,
    fs,
    path::PathBuf,
    process::{Command, Stdio},
};

use which::which;

fn main() -> Result<(), Box<dyn Error>> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    let args: Vec<&str> = args.iter().map(|s| &**s).collect();

    match &args[..] {
        &["regenerate-test-vectors"] => {
            regenerate_test_vectors()?;
        }
        _ => {
            eprintln!("usage: cargo xtask regenerate-test-vectors");
            return Err("invalid usage".into());
        }
    }

    Ok(())
}

fn locate_ruby() -> Result<PathBuf, Box<dyn Error>> {
    Ok(which("ruby")?)
}

fn regenerate_test_vectors() -> Result<(), Box<dyn Error>> {
    let ruby_path = locate_ruby()?;

    let (dir_listing, load_path) = {
        if let Ok(dir_listing) = fs::read_dir("tests/test-vectors") {
            (dir_listing, PathBuf::from("../xtask/ruby_include"))
        } else if let Ok(dir_listing) = fs::read_dir("ruby-marshal/tests/test-vectors") {
            (dir_listing, PathBuf::from("xtask/ruby_include"))
        } else {
            return Err("failed to find test vectors directory; ensure your current directory is within the workspace".into());
        }
    };
    let load_path = load_path.canonicalize()?;

    for file in dir_listing {
        let file = file?;
        if !file.file_type()?.is_file() {
            continue;
        }

        let file_path = file.path();
        let Some(extension) = file_path.extension() else { continue; };
        if extension != "rb" {
            continue;
        }

        eprintln!("{}", file_path.display());

        let ruby_opts = RubyOptions {
            ruby_path: ruby_path.clone(),
            script: file_path,
            load_path: load_path.clone(),
        };

        run_ruby(&ruby_opts)?;
    }

    Ok(())
}

struct RubyOptions {
    ruby_path: PathBuf,
    script: PathBuf,
    load_path: PathBuf,
}

fn run_ruby(options: &RubyOptions) -> Result<(), Box<dyn Error>> {
    let mut cmd = Command::new(&options.ruby_path);
    let cmd = cmd
        .args([
            OsStr::new("-I"),
            options.load_path.as_os_str(),
            options.script.file_name().unwrap(),
        ])
        .current_dir(options.script.parent().unwrap())
        .stdin(Stdio::null());

    /*let args = cmd
    .get_args()
    .map(|a| a.to_string_lossy().to_string())
    .collect::<Vec<_>>()
    .join(" ");*/
    //eprintln!("{} {args}", options.ruby_path.display());

    cmd.spawn()?.wait()?;

    Ok(())
}
