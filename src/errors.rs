use std::num::ParseIntError;

use thiserror::Error;

use crate::{types::{ClarityType, TryIntoClarityIntError}, ast::Op};

#[derive(Error, Default, Debug, Clone, PartialEq)]
pub enum ClarityError {
    #[default]
    #[error("an unexpected error has occurred and no additionl information is available")]
    Undefined,

    //#[error("an error occurred while parsing a refined integer definition")]
    //RefinedIntegerParsingFailed,
    #[error(
        "an error occurred while attempting to convert '{from:?}' to a ClarityInteger: {inner:?}"
    )]
    IntoClarityInteger {
        from: String,
        inner: TryIntoClarityIntError,
    },

    #[error("an error occurred while trying to parse a `string-ascii` or `string-utf8` definition")]
    ParseStringDefinition,

    #[error("arithmetic overflow occurred during execution of `{op:?}`")]
    ArithmeticOverflow { op: Op },
    #[error("arithmetic underflow occurred during execution of `{op:?}`")]
    ArithmeticUnderflow { op: Op },

    #[error("an error occurred while attempting to parse an integer: {inner:?}")]
    ParseInt { inner: ParseIntError },

    #[error("type mismatch: expected <{expected:?}> but got <{received:?}>")]
    TypeMismatch {
        expected: ClarityType,
        received: ClarityType,
    },
}
