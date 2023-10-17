/*use crate::{types::{ClarityInteger, Value}, value_ext::ValueExtensions, ast::{Define, Op, Literal, SExpr}};
use anyhow::{bail, Result};

impl SExpr {
    /// Entrypoint for contract evaluation. Expects the contract to be wrapped
    /// in an outer/top-level closure. This function will evaluate each top-level
    /// contract expression and return an ordered list of results.
    pub fn eval(&self) -> Result<Vec<Value>> {
        let mut values: Vec<Value> = Default::default();

        if let SExpr::Closure(top_level) = self {
            for expr in top_level {
                let value = expr.eval_inner()?;
                values.push(value);
            }
        }

        Ok(values)
    }

    /// Inner contract evaluation function which handles top-level expressions
    /// and routes them further to specific evaluation functions.
    fn eval_inner(&self) -> Result<Value> {
        match self {
            SExpr::Literal(lit) => Self::eval_literal(lit),
            SExpr::Closure(exprs) => match &exprs[..] {
                [SExpr::Define(_), ..] => Self::eval_defines(exprs),
                [SExpr::Op(_), ..] => Self::eval_ops(exprs),
                _ => bail!("cannot evaluate closure, no match found: {self:?}"),
            },
            _ => bail!("cannot evaluate operator: {self:?}"),
        }
    }

    /// Evaluates a literal.
    fn eval_literal(lit: &Literal) -> Result<Value> {
        match lit {
            Literal::Integer(int) => Ok(match int {
                ClarityInteger::I32(i) => Value::Integer(ClarityInteger::I32(*i)),
                ClarityInteger::U32(i) => Value::Integer(ClarityInteger::U32(*i)),
                ClarityInteger::I64(i) => Value::Integer(ClarityInteger::I64(*i)),
                ClarityInteger::U64(i) => Value::Integer(ClarityInteger::U64(*i)),
                // These are the default integer types in Clarity which we are
                // remapping to the `Integer` variant. `Value::Int` and `Value::UInt`
                // become aliases.
                ClarityInteger::I128(i) => Value::Integer(ClarityInteger::I128(*i)),
                ClarityInteger::U128(i) => Value::Integer(ClarityInteger::U128(*i)),
                // The Clarity `Value` type would need to be extended to have a type
                // similar to the `ClarityInteger` type here in order to support
                // integers larger than 128 bits. We use our simulated `Value` type here.
                ClarityInteger::I256(i) => Value::Integer(ClarityInteger::I256(i.clone())),
                ClarityInteger::U256(i) => Value::Integer(ClarityInteger::U256(i.clone())),
                ClarityInteger::I512(i) => Value::Integer(ClarityInteger::I512(i.clone())),
                ClarityInteger::U512(i) => Value::Integer(ClarityInteger::U512(i.clone())),
            }),
            _ => bail!("literal type {lit:?} not yet implemented")
        }
    }

    /// Evaluation of define-* statements.
    fn eval_defines(exprs: &[SExpr]) -> Result<Value> {
        match &exprs[..] {
            // DEFINE-MAP
            [SExpr::Define(Define::Map(def)), name, key_ty, val_ty] => {
                eprintln!("DEFINE-MAP: name={name:?}, key_ty={key_ty:?}, val_ty={val_ty:?}");
                Ok(Value::Null)
            }
            // DEFINE READ-ONLY FUNCTION
            [SExpr::Define(Define::ReadOnlyFunction), signature, body] => {
                eprintln!("DEFINE-READ-ONLY-FUNCTION: signature={signature:?}, body={body:?}");
                Ok(Value::Null)
            }
            // DEFINE PUBLIC FUNCTION
            [SExpr::Define(Define::PublicFunction), signature, body] => {
                eprintln!("DEFINE-PUBLIC-FUNCTION: signature={signature:?}, body={body:?}");
                Ok(Value::Null)
            }
            // DEFINE PRIVATE FUNCTION
            [SExpr::Define(Define::PrivateFunction), signature, body] => {
                eprintln!("DEFINE-PRIVATE-FUNCTION: signature={signature:?}, body={body:?}");
                Ok(Value::Null)
            }
            _ => bail!("define function not yet implemented.")
        }
    }

    /// Evaluation of operations (Clarity functions).
    fn eval_ops(exprs: &[SExpr]) -> Result<Value> {
        match &exprs[..] {
            // ADDITION
            [SExpr::Op(Op::Add), init, tail @ ..] => {
                tail.iter().fold(Self::eval_inner(init), |acc, expr| {
                    acc.and_then(|a| Self::eval_inner(expr).map(|v| a.checked_add(v))?)
                })
            }
            // SUBTRACTION
            [SExpr::Op(Op::Sub), init, tail @ ..] => {
                tail.iter().fold(Self::eval_inner(init), |acc, expr| {
                    acc.and_then(|a| Self::eval_inner(expr).map(|v| a.checked_sub(v))?)
                })
            }
            // MULTIPLICATION
            [SExpr::Op(Op::Mul), init, tail @ ..] => {
                tail.iter().fold(Self::eval_inner(init), |acc, expr| {
                    acc.and_then(|a| Self::eval_inner(expr).map(|v| a.checked_mul(v))?)
                })
            }
            // DIVISION
            [SExpr::Op(Op::Div), init, tail @ ..] => {
                tail.iter().fold(Self::eval_inner(init), |acc, expr| {
                    acc.and_then(|a| Self::eval_inner(expr).map(|v| a.checked_div(v))?)
                })
            },
            _ => bail!("op not yet implemented: {exprs:?}")
        }
    }
}
*/
