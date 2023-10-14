use thiserror::Error;

use crate::types::ClarityType;

#[derive(Error, Debug, Clone, Copy, PartialEq)]
pub enum ClarityError {
    #[error("type mismatch: expected <{expected:?}> but got <{received:?}>")]
    TypeMismatch {
        expected: ClarityType,
        received: ClarityType,
    },
}
