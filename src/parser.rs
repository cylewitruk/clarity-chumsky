use chumsky::{input::ValueInput, prelude::*};

use crate::{expressions::SExpr, tokens::Token};

pub fn parser<'a, I>() -> impl Parser<'a, I, SExpr, extra::Err<Rich<'a, Token>>>
where
    I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
    recursive(|sexpr| {
        let atom = select! {
            Token::OpAdd => SExpr::Add,
            Token::OpSub => SExpr::Sub,
            Token::OpMul => SExpr::Mul,
            Token::OpDiv => SExpr::Div,
            Token::LiteralInteger(ty) => SExpr::LiteralInteger(ty)
        };

        let list = sexpr
            .repeated()
            .collect()
            .map(SExpr::List)
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose));

        atom.or(list)
    })
}
