use clarity::vm::Value;

use crate::{IntegerType, value_ext::ValueExtensions, ClarityInteger};
use anyhow::{anyhow, bail, Result};

#[derive(Debug)]
pub enum SExpr {
    LiteralInteger(ClarityInteger),
    List(Vec<Self>),

    // Operators
    Add,
    Sub,
    Mul,
    Div,
}

impl SExpr {
    // Recursively evaluate an s-expression
    pub fn eval(&self) -> Result<Value> {
        match self {
            SExpr::LiteralInteger(ty) => match ty {
                ClarityInteger::I128(i) => Ok(Value::Int(*i)),
                ClarityInteger::U128(i) => Ok(Value::UInt(*i)),
            },
            SExpr::List(list) => match &list[..] {
                // ADD
                [SExpr::Add, tail @ ..] => {
                    tail[1..].iter().fold(
                        Self::eval(&tail[0]),
                        |acc, expr| {
                            if acc.is_err() { return acc }
                            let val = Self::eval(expr)?;
                            val.checked_add(acc.unwrap())
                        }
                    )
                }
                // SUBTRACT
                [SExpr::Sub, tail @ ..] => {
                    tail[1..].iter().fold(
                        Self::eval(&tail[0]),
                        |acc, expr| {
                            if acc.is_err() { return acc }
                            let val = Self::eval(expr)?;
                            acc.unwrap().checked_sub(val)
                        }
                    )
                }
                // MULTIPLY
                [SExpr::Mul, tail @ ..] => {
                    tail[1..].iter().fold(
                        Self::eval(&tail[0]),
                        |acc, expr| {
                            if acc.is_err() { return acc }
                            let val = Self::eval(expr)?;
                            if acc.is_err() { return acc }
                            val.checked_mul(acc.unwrap())
                        }
                    )
                }
                // DIVIDE
                [SExpr::Div, tail @ ..] => {
                    tail[1..].iter().fold(
                        Self::eval(&tail[0]),
                        |acc, expr| {
                            if acc.is_err() { return acc }
                            let val = Self::eval(expr)?;
                            acc.unwrap().checked_div(val)
                        }
                    )
                }
                _ => bail!("cannot evaluate list, no match found"),
            },
            _ => bail!("cannot evaluate operator: {self:?}")
        }
    }
}
