//! Macros for testing conditions without panicking. The `expect_*` family of macros cause an early
//! return of an [`anyhow::Error`] if the expected condition is not met.

use anyhow::anyhow;

#[doc(hidden)]
pub fn msg(file: &str, line: u32, expr: &str, msg: &str) -> anyhow::Error {
    anyhow!("\n\n\x1B[1m[{file}:{line}]\x1B[0m \x1B[4m{expr}\x1B[0m: \x1B[31m{msg}\x1B[0m\n")
}

/// Expects that the given condition evaluates to `true`; otherwise returns early.
///
/// # Examples
///
/// ```
/// # use anyhow::Result;
/// # use expecting::expect;
/// fn passing_test() -> Result<()> {
///     expect!(1 + 1 == 2);
///     Ok(())
/// }
/// # assert!(passing_test().is_ok());
///
/// fn failing_test() -> Result<()> {
///     expect!(1 + 1 == 69);  // returns early
///     Ok(())  // won't be reached
/// }
/// # assert!(failing_test().is_err());
/// ```
///
/// `failing_test()` will return early after calling `expect!`. The `Err` will be wrapped in a
/// descriptive error message such as:
///
/// > **[my/file.rs:12]** *"expect!(condition)"* Expected true but was false.<br/>
/// > [ ... wrapped Err details ...]
///
#[macro_export]
macro_rules! expect {
    ( $a:expr ) => {{
        if $a {
            Ok(())
        } else {
            let expr_str = format!("expect({})", stringify!($a));
            let msg = format!("Expected true but was false.");
            Err($crate::msg(file!(), line!(), &expr_str, &msg))
        }
    }?};
}

/// Expects that the given [`Result`] is `Ok` and returns its unwrapped contents; otherwise returns
/// early.
///
/// # Examples
///
/// ```
/// # use anyhow::{anyhow, Result};
/// # use expecting::{expect_eq, expect_ok};
/// fn passing_test() -> Result<()> {
///     let result: Result<i32> = Ok(69);
///     let contents = expect_ok!(result);
///     expect_eq!(contents, 69);
///     Ok(())
/// }
/// # assert!(passing_test().is_ok());
///
/// fn failing_test() -> Result<()> {
///     let result: Result<i32> = Err(anyhow!("ruh roh!"));
///     let contents = expect_ok!(result);  // returns early
///     Ok(())  // won't be reached
/// }
/// # assert!(failing_test().is_err());
/// ```
///
/// `failing_test()` will return early after calling `expect_ok!`. The `Err` will be wrapped in a
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

/// Expects that the given [`Result`] is `Err` and returns the unwrapped error; otherwise returns
/// early.
///
/// # Examples
///
/// ```
/// # use anyhow::{anyhow, Result};
/// # use expecting::{expect, expect_err};
/// fn passing_test() -> Result<()> {
///     let result: Result<i32> = Err(anyhow!("ruh roh!"));
///     let err = expect_err!(result);
///     expect!(err.to_string().contains("ruh roh!"));
///     Ok(())
/// }
/// # assert!(passing_test().is_ok());
///
/// fn failing_test() -> Result<()> {
///     let err = expect_err!(Ok(()));  // returns early
///     Ok(())  // won't be reached
/// }
/// # assert!(failing_test().is_err());
/// ```
///
/// `failing_test()` will return early after calling `expect_err!`. The `Err` will be wrapped in a
/// descriptive error message such as:
///
/// > **[my/file.rs:12]** *"expect_err!(result)"* Expected Err, got Ok: [ contents ]<br/>
/// > [ ... wrapped Err details ...]
///
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

/// Expects that the given [`Option`] is `Some` and returns its unwrapped contents; otherwise
/// returns early.
///
/// # Examples
///
/// ```
/// # use anyhow::Result;
/// # use expecting::{expect_eq, expect_some};
/// fn passing_test() -> Result<()> {
///     let option = Some(69);
///     let contents = expect_some!(option);
///     expect_eq!(contents, 69);
///     Ok(())
/// }
/// # assert!(passing_test().is_ok());
///
/// fn failing_test() -> Result<()> {
///     let option = None::<()>;
///     let contents = expect_some!(option);  // returns early with Err
///     Ok(())  // won't be reached
/// }
/// # assert!(failing_test().is_err());
/// ```
///
/// `failing_test()` will return early after calling `expect_some!`. The `Err` will be wrapped in a
/// descriptive error message such as:
///
/// > **[my/file.rs:12]** *"expect_some!(option)"* Expected Some, got None"<br/>
/// > [ ... wrapped Err details ...]
///
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

/// Expects that the given [`Option`] is `None`; otherwise returns early.
///
/// # Examples
///
/// ```
/// # use anyhow::Result;
/// # use expecting::expect_none;
/// fn passing_test() -> Result<()> {
///     expect_none!(None::<()>);
///     Ok(())
/// }
/// # assert!(passing_test().is_ok());
///
/// fn failing_test() -> Result<()>{
///     expect_none!(Some(()));  // returns early
///     Ok(())  // won't be reached
/// }
/// # assert!(failing_test().is_err());
/// ```
///
/// `failing_test()` will return early after calling `expect_none!`. The `Err` will be wrapped in a
/// descriptive error message such as:
///
/// > **[my/file.rs:12]** *"expect_none!(option)"* Expected None, got Some: [ contents ]"<br/>
/// > [ ... wrapped Err details ...]
///
#[macro_export]
macro_rules! expect_none {
    ( $option:expr ) => {
        match $option {
            None => Ok(()),
            Some(t) => {
                let expr_str = format!("expect_none({})", stringify!($option));
                let msg = format!("Expected None, got Some:\n{t:?})");
                Err($crate::msg(file!(), line!(), &expr_str, &msg))
            }
        }?
    };
}

/// Expects that a == b; otherwise returns early.
///
/// # Examples
///
/// ```
/// # use anyhow::Result;
/// # use expecting::expect_eq;
///
/// fn passing_test() -> Result<()> {
///     expect_eq!(1, 1);
///     Ok(())
/// }
/// # assert!(passing_test().is_ok());
///
/// fn failing_test() -> Result<()> {
///     expect_eq!(1, 2);  // returns early
///     Ok(())  // won't be reached
/// }
/// # assert!(failing_test().is_err());
/// ```
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

/// Expects that a != b; otherwise returns early.
///
/// # Examples
///
/// ```
/// # use anyhow::Result;
/// # use expecting::expect_ne;
///
/// fn passing_test() -> Result<()> {
///     expect_ne!(1, 2);
///     Ok(())
/// }
/// # assert!(passing_test().is_ok());
///
/// fn failing_test() -> Result<()> {
///     expect_ne!(1, 1);  // returns early
///     Ok(())  // won't be reached
/// }
/// # assert!(failing_test().is_err());
/// ```
#[macro_export]
macro_rules! expect_ne {
    ( $a:expr, $b:expr ) => {{
        if $a != $b {
            Ok(())
        } else {
            let expr_str = format!("expect_ne({}, {})", stringify!($a), stringify!($b));
            let msg = format!("{:?} == {:?}, expected them *not* to be equal.", $a, $b);
            Err($crate::msg(file!(), line!(), &expr_str, &msg))
        }
    }?};
}

/// Expects that the given container (e.g., [`Vec`]) is empty; otherwise returns early.
///
/// # Examples
///
/// ```
/// # use anyhow::Result;
/// # use expecting::expect_empty;
///
/// fn passing_test() -> Result<()> {
///     let empty: Vec<i32> = vec![];
///     expect_empty!(empty);
///     Ok(())
/// }
/// # assert!(passing_test().is_ok());
///
/// fn failing_test() -> Result<()> {
///     expect_empty!(vec![0, 1, 1, 2, 3, 5, 8, 13, 21]);  // returns early
///     Ok(())  // won't be reached
/// }
/// # assert!(failing_test().is_err());
/// ```
#[macro_export]
macro_rules! expect_empty {
    ( $a:expr ) => {{
        if $a.is_empty() {
            Ok(())
        } else {
            let expr_str = format!("expect_empty({})", stringify!($a));
            let msg = format!("Expected empty, but contained elements:\n{:?}", $a);
            Err($crate::msg(file!(), line!(), &expr_str, &msg))
        }
    }?};
}

/// Expects that the given container (e.g., [`Vec`]) contains the element or given string contains
/// the substring; otherwise returns early.
///
/// # Examples
///
/// ```
/// # use anyhow::Result;
/// # use expecting::expect_contains;
///
/// fn passing_test() -> Result<()> {
///     let v: Vec<i32> = vec![42, 1337];
///     expect_contains!(v, 42);
///     Ok(())
/// }
/// # assert!(passing_test().is_ok());
///
/// fn passing_test_for_string() -> Result<()> {
///     let superstring = "angelheaded hipsters";
///     expect_contains!(superstring, "hip");
///     Ok(())
/// }
/// # assert!(passing_test_for_string().is_ok());
///
/// fn failing_test() -> Result<()> {
///     let v: Vec<i32> = vec![42, 1337];
///     expect_contains!(v, 13);  // returns early
///     Ok(())  // won't be reached
/// }
/// # assert!(failing_test().is_err());
/// ```
#[macro_export]
macro_rules! expect_contains {
    ( $container:expr, $element_or_substr:expr ) => {{
        if $container.contains(&$element_or_substr) {
            Ok(())
        } else {
            let expr_str = format!(
                "expect_contains({}, {})",
                stringify!($container),
                stringify!($element_or_substr)
            );
            let msg = format!(
                "Expected to contain {:?}, but did not:\n{:?}",
                $element_or_substr, $container,
            );
            Err($crate::msg(file!(), line!(), &expr_str, &msg))
        }
    }?};
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use anyhow::{anyhow, Result};

    #[test]
    fn expect__success__no_early_return() {
        let test = || -> Result<()> {
            expect!(1 + 1 == 2);
            Ok(())
        };
        assert!(test().is_ok());
    }

    #[test]
    fn expect__failure__causes_early_return() {
        let test = || -> Result<()> {
            expect!(1 + 1 == 69); // should return early
            Ok(())
        };
        assert!(test().is_err());
    }

    #[test]
    fn expect_ok__success__returns_ok_value() {
        let test = || -> Result<i64> {
            let result: Result<i64> = Ok(69);
            let contents = expect_ok!(result);
            Ok(contents)
        };
        let result = test();
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 69);
    }

    #[test]
    fn expect_ok__failure__causes_early_return() {
        let test = || -> Result<()> {
            let result: Result<i64> = Err(anyhow!("ruh roh!"));
            let _ = expect_ok!(result); // returns early with Err
            Ok(()) // won't be reached
        };
        assert!(test().is_err());
    }

    #[test]
    fn expect_err__success__returns_err_value() {
        let test = || -> Result<anyhow::Error> {
            let result: Result<i64> = Err(anyhow!("ruh roh!"));
            let err = expect_err!(result);
            Ok(err)
        };
        let result = test();
        assert!(result.is_ok());
        assert!(result.unwrap().to_string().contains("ruh roh!"));
    }

    #[test]
    fn expect_err__failure__causes_early_return() {
        let test = || -> Result<()> {
            let result: Result<i64> = Ok(69);
            let _ = expect_err!(result); // returns early with Err
            Ok(()) // won't be reached
        };
        assert!(test().is_err());
    }

    #[test]
    fn expect_some__success__returns_some_value() {
        let test = || -> Result<i32> {
            let some = Some(1337);
            let contents = expect_some!(some);
            Ok(contents)
        };
        let result = test();
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 1337);
    }

    #[test]
    fn expect_some__failure__causes_early_return() {
        let test = || -> Result<()> {
            let _ = expect_some!(None::<i32>); // returns early with Err
            Ok(()) // won't be reached
        };
        assert!(test().is_err());
    }

    #[test]
    fn expect_none__success__no_early_return() {
        let test = || -> Result<()> {
            expect_none!(None::<i64>);
            Ok(())
        };
        assert!(test().is_ok());
    }

    #[test]
    fn expect_none__failure__causes_early_return() {
        let test = || -> Result<()> {
            expect_none!(Some(1337)); // returns early with Err
            Ok(()) // won't be reached
        };
        assert!(test().is_err());
    }

    #[test]
    fn expect_eq__success__no_early_return() {
        let test = || -> Result<()> {
            expect_eq!(1, 1);
            Ok(())
        };
        assert!(test().is_ok());
    }

    #[test]
    fn expect_eq__failure__causes_early_return() {
        let test = || -> Result<()> {
            expect_eq!(1, 2); // returns early with Err
            Ok(()) // won't be reached
        };
        assert!(test().is_err());
    }

    #[test]
    fn expect_ne__success__no_early_return() {
        let test = || -> Result<()> {
            expect_ne!(1, 2);
            Ok(())
        };
        assert!(test().is_ok());
    }

    #[test]
    fn expect_ne__failure__causes_early_return() {
        let test = || -> Result<()> {
            expect_ne!(1, 1); // returns early with Err
            Ok(()) // won't be reached
        };
        assert!(test().is_err());
    }

    #[test]
    fn expect_empty__success__no_early_return() {
        let test = || -> Result<()> {
            let empty: Vec<i64> = vec![];
            expect_empty!(empty);
            Ok(())
        };
        assert!(test().is_ok());
    }

    #[test]
    fn expect_empty__failure__causes_early_return() {
        let test = || -> Result<()> {
            let not_empty: Vec<i64> = vec![1];
            expect_empty!(not_empty); // should return early
            Ok(())
        };
        assert!(test().is_err());
    }

    #[test]
    fn expect_contains__vec_of_int_success__no_early_return() {
        let test = || -> Result<()> {
            let v: Vec<i64> = vec![42, 1337];
            expect_contains!(v, 42);
            Ok(())
        };
        assert!(test().is_ok());
    }

    #[test]
    fn expect_contains__vec_of_int_failure__causes_early_return() {
        let test = || -> Result<()> {
            let v: Vec<i64> = vec![42, 1337];
            expect_contains!(v, 69);
            Ok(())
        };
        assert!(test().is_err());
    }

    #[test]
    fn expect_contains__string_success__no_early_return() {
        let test = || -> Result<()> {
            let superstring = "angelheaded hipsters burning for the ancient heavenly connection";
            expect_contains!(superstring, "hipsters");
            Ok(())
        };
        assert!(test().is_ok());
    }

    #[test]
    fn expect_contains__string_failure__causes_early_return() {
        let test = || -> Result<()> {
            let superstring = "angelheaded hipsters burning for the ancient heavenly connection";
            expect_contains!(superstring, "yuppies");
            Ok(())
        };
        assert!(test().is_err());
    }

    #[test]
    fn expect_contains__string_failure__returns_correct_err_message() {
        let test = || -> Result<()> {
            let superstring = "angelheaded hipsters burning";
            expect_contains!(superstring, "yuppies");
            Ok(())
        };
        let result = test();
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains(
            "Expected to contain \"yuppies\", but did not:\n\"angelheaded hipsters burning\""
        ));
    }
}
