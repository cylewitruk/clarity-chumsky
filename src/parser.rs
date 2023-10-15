use chumsky::{input::ValueInput, prelude::*, extra::{State, Full, Err}, error::Error};

use crate::{
    expressions::{SExpr, Define, Op, Type, Literal, Keyword}, 
    lexer::Token, signatures::{MapSignature, FunctionSignature}
};

pub struct ParsingState {
    maps: Vec<MapSignature>,
    functions: Vec<FunctionSignature>
}

impl Default for ParsingState {
    fn default() -> Self {
        Self { 
            maps: Default::default(), 
            functions: Default::default() 
        }
    }
}

pub fn parser<'a, I>() -> impl Parser<'a, I, SExpr, Full::<Rich<'a, Token<'a>>, ParsingState, ()>>
where
    I: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan>,
{

    recursive(|sexpr| {

        // Define functions
        let top_level_fns = select! {
            Token::OpDefineMap => SExpr::Define(Define::Map),
            Token::OpDefineReadOnly => SExpr::Define(Define::ReadOnlyFunction),
            Token::OpDefinePublic => SExpr::Define(Define::PublicFunction),
            Token::OpDefinePrivate => SExpr::Define(Define::PrivateFunction),
            Token::OpDefineDataVar => SExpr::Define(Define::DataVar),
        };

        let keywords = select! {
            Token::BlockHeight => SExpr::Keyword(Keyword::BlockHeight),
            Token::BurnBlockHeight => SExpr::Keyword(Keyword::BurnBlockHeight),
            Token::ChainId => SExpr::Keyword(Keyword::ChainId),
            Token::ContractCaller => SExpr::Keyword(Keyword::ContractCaller),
            Token::False => SExpr::Keyword(Keyword::False),
            Token::IsInMainnet => SExpr::Keyword(Keyword::IsInMainnet),
            Token::IsInRegTest => SExpr::Keyword(Keyword::IsInRegTest),
            Token::None => SExpr::Keyword(Keyword::None),
            Token::StxLiquidSupply => SExpr::Keyword(Keyword::StxLiquidSupply),
            Token::True => SExpr::Keyword(Keyword::True),
            Token::TxSender => SExpr::Keyword(Keyword::TxSender),
            Token::TxSponsorOpt => SExpr::Keyword(Keyword::TxSponsor),
        };

        let identifier = select! {
            Token::Identifier(name) => SExpr::Identifier(name)
        };
        
        let types = select! {
            Token::Int => SExpr::TypeDef(Type::Int),
            Token::UInt => SExpr::TypeDef(Type::UInt),
            Token::Principal => SExpr::TypeDef(Type::Principal),
            Token::RefinedInteger(x) => SExpr::RefinedInteger(x),
            Token::AsciiString(len) => SExpr::TypeDef(Type::StringAscii(len)),
            Token::Utf8String(len) => SExpr::TypeDef(Type::StringUtf8(len))
        };

        let ops = select! {
            Token::OpAdd => SExpr::Op(Op::Add),
            Token::OpSub => SExpr::Op(Op::Sub),
            Token::OpMul => SExpr::Op(Op::Mul),
            Token::OpDiv => SExpr::Op(Op::Div),
            Token::OpDefaultTo => SExpr::Op(Op::DefaultTo),
            Token::OpMapGetOpt => SExpr::Op(Op::MapGet),
            Token::OpOk => SExpr::Op(Op::Ok),
            Token::OpMapSet => SExpr::Op(Op::MapSet),
        };

        let literals = select! {
            Token::Int => SExpr::Literal(Literal::Int),
            Token::UInt => SExpr::Literal(Literal::UInt),
            Token::LiteralInteger(int) => SExpr::Literal(Literal::Integer(int))
        };
        

        let list = sexpr
            .repeated()
            .collect()
            .map(SExpr::Closure)
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose));

        list.clone().map(|l| {
            eprintln!("expr: {l:?}");
        });

        top_level_fns
            .or(keywords)
            .or(ops)
            .or(types)
            .or(identifier)
            .or(literals)
            .or(list)
    })
}
