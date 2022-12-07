//! Macros for testing conditions without panicking. The `expect_*` family of macros cause an early
//! return of an [`anyhow::Error`] if the expected condition is not met.

use anyhow::anyhow;

#[doc(hidden)]
pub fn msg(file: &str, line: u32, expr: &str, msg: &str) -> anyhow::Error {
    anyhow!("\n\n\x1B[1m[{file}:{line}]\x1B[0m \x1B[4m{expr}\x1B[0m: \x1B[31m{msg}\x1B[0m\n")
}

/// Expects that the given [`Result`] is Ok and returns its contents; otherwise returns early.
///
/// # Examples
///
/// This test passes because `result` is `Ok`:
///
/// ```
/// # use anyhow::Result;
/// # use expecting::expect_ok;
///
/// #[test]
/// fn passing_test() -> Result<()> {
///     let result: Result<i64> = Ok(69);
///     let contents = expect_ok!(result);
///     assert_eq!(contents, 69);
///     Ok(())
/// }
/// ```
///
/// Note: We use `assert_eq!` just as an example, but if you are using `expect_*`, you generally
/// wouldn't use `assert_*`.
///
/// This test fails because `result` is `Err`:
///
/// ```
/// # use anyhow::{anyhow, Result};
/// # use expecting::expect_ok;
///
/// #[test]
/// fn failing_test() -> Result<()> {
///     let result: Result<i64> = Err(anyhow!("ruh roh!"));
///     let contents = expect_ok!(result);  // returns early with Err
///     Ok(())  // won't be reached
/// }
/// ```
///
/// The above test will return early after calling `expect_ok!`. The `Err` will be wrapped in a
/// descriptive error message such as:
///
/// > **[my/file.rs:12]** *"expect_ok!(result)"* Expected Ok, got Err: "ruh roh!"<br/>
/// > [ ... wrapped Err details ...]
///
#[macro_export]
macro_rules! expect_ok {
    ( $result:expr ) => {
        match $result {
            Ok(t) => Ok(t),
            Err(ref e) => {
                let expr_str = format!("expect_ok({})", stringify!($result));
                let msg = format!("Expected Ok, got Err:\n{e:?})");
                Err($crate::msg(file!(), line!(), &expr_str, &msg))
            }
        }?
    };
}

#[macro_export]
macro_rules! expect_err {
    ( $result:expr ) => {
        match $result {
            Err(e) => Ok(e),
            Ok(t) => {
                let expr_str = format!("expect_err({})", stringify!($result));
                let msg = format!("Expected Err, got Ok:\n{t:?}");
                Err($crate::msg(file!(), line!(), &expr_str, &msg))
            }
        }?
    };
}

#[macro_export]
macro_rules! expect_some {
    ( $option:expr ) => {
        match $option {
            Some(t) => Ok(t),
            None => {
                let expr_str = format!("expect_some({})", stringify!($option));
                let msg = format!("Expected Some, got None");
                Err($crate::msg(file!(), line!(), &expr_str, &msg))
            }
        }?
    };
}

#[macro_export]
macro_rules! expect_eq {
    ( $a:expr, $b:expr ) => {{
        if $a == $b {
            Ok(())
        } else {
            let expr_str = format!("expect_eq({}, {})", stringify!($a), stringify!($b));
            let msg = format!("{:?} != {:?}, expected them to be equal.", $a, $b);
            Err($crate::msg(file!(), line!(), &expr_str, &msg))
        }
    }?};
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use anyhow::{anyhow, Result};

    #[test]
    fn expect_ok__success__returns_ok_value() -> Result<()> {
        let result: Result<i64> = Ok(69);
        let contents = expect_ok!(result);
        assert_eq!(contents, 69);
        Ok(())
    }

    #[test]
    fn expect_ok__failure__causes_early_return() {
        let test = || -> Result<()> {
            let result: Result<i64> = Err(anyhow!("ruh roh!"));
            let _ = expect_ok!(result); // returns early with Err
            Ok(()) // won't be reached
        };
        let result = test();
        assert!(result.is_err());
    }
}
