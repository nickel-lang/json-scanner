use json_scanner::Parser;
use libtest_mimic::{Arguments, Trial};
use std::{path::Path, process::ExitCode};

pub fn main() -> ExitCode {
    let args = Arguments::from_args();
    let inputs_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/inputs");

    let mut trials = Vec::new();

    for entry in std::fs::read_dir(inputs_dir).unwrap() {
        let entry = entry.unwrap();
        if entry.path().extension() == Some("json".as_ref()) {
            let name = entry.file_name();
            let name = name.as_os_str().to_string_lossy();
            let expect_success = name.starts_with("y_");
            trials.push(Trial::test(name, move || {
                let contents = std::fs::read(entry.path()).unwrap();
                let mut parser = Parser::new(&contents);
                let mut err = None;
                let mut events = Vec::new();

                loop {
                    match parser.next_event() {
                        Err(e) => {
                            err = Some(e);
                            break;
                        }
                        Ok(None) => {
                            break;
                        }
                        Ok(e) => {
                            events.push(e);
                        }
                    }
                }

                if expect_success && let Some(err) = err {
                    panic!("unexpected error {err:?}");
                } else if !expect_success && err.is_none() {
                    panic!("unexpected success {events:?}");
                };
                Ok(())
            }));
        }
    }

    libtest_mimic::run(&args, trials).exit_code()
}
