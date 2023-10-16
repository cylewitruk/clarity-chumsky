use chumsky::{input::ValueInput, prelude::*, extra::Full};

use crate::{
    ast::SExpr, 
    lexer::Token, signatures::{MapSignature, FunctionSignature}, ast::{Literal, Define, Type, MapDef, FuncArg, FuncSignature, Op, DefaultToDef}, types::{FunctionKind, ClarityInteger}
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

pub fn parser<'a, I>() -> impl Parser<
    'a, 
    I, 
    SExpr, 
    Full::<Rich<'a, Token>, 
    ParsingState, ()>
>
where
    I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{

    recursive(|sexpr| {

        let ident = select! { 
            Token::Identifier(ident) => ident 
        }.labelled("identifier");

        let ty = select! {
            Token::Int => Type::Int,
            Token::UInt => Type::UInt,
            Token::Principal => Type::Principal
        }.labelled("type");

        let fn_visibility = select! {
            Token::OpDefinePublic => FunctionKind::Public,
            Token::OpDefinePrivate => FunctionKind::Private,
            Token::OpDefineReadOnly => FunctionKind::ReadOnly
        }.labelled("function definition");

        

        let fn_signature = ident
            .then(ident.then(ty))
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .repeated();

        let items = sexpr
            .clone()
            .separated_by(just(Token::Whitespace))
            .allow_leading()
            .allow_trailing()
            .collect::<Vec<_>>();

        let define_map = just(Token::OpDefineMap) 
            .ignore_then(ident)
            .then(ty.labelled("key-type"))
            .then(ty.labelled("value-type"))
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|((name, key_ty), val_ty)| {
                eprintln!("define-map {} {:?} {:?}", name, key_ty, val_ty);
                SExpr::Define(Define::Map(MapDef { name, key_ty, val_ty }))
            });

        let define_fn = fn_visibility
            .then(fn_signature)
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|x| {
                todo!()
            });
            
            

        // Define functions
        /*let top_level_fns = select! {
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
        });*/

        define_map
            .or(define_fn)

        /*top_level_fns
            .or(keywords)
            .or(ops)
            .or(types)
            .or(identifier)
            .or(literals)
            .or(list)*/
    }).then_ignore(end())
}

// The type of the input that our parser operates on. The input is the `&[(Token, Span)]` token buffer generated by the
// lexer, wrapped in a `SpannedInput` which 'splits' it apart into its constituent parts, tokens and spans, for chumsky
// to understand.
//type ParserInput<'tokens> =
 //   chumsky::input::SpannedInput<Token, Span, &'tokens [(Token, Span)]>;


pub type Span = SimpleSpan<usize>;
//pub type Spanned<T> = (T, Span);

pub fn literal_parser<'a, I>() -> impl Parser<'a, I, Literal, extra::Err<Rich<'a, Token, Span>>> + Clone
where
    I: ValueInput<'a, Token = Token, Span = SimpleSpan>
{
    select! {
        Token::LiteralAsciiString(str) => Literal::AsciiString(str),
        Token::LiteralUtf8String(str) => Literal::Utf8String(str),
        Token::LiteralInteger(int) => Literal::Integer(int)
    }
}

fn expr_parser<'a, I>() -> 
impl Parser<'a, I, SExpr, extra::Err<Rich<'a, Token>>>
where
    I: ValueInput<'a, Token = Token, Span = SimpleSpan>
{
    recursive(|expr| {
        let default_to = just(Token::OpDefaultTo)
            .ignore_then(literal_parser())
            .then(expr)
            .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
            .map(|(default, tail)| {
                eprintln!("default: {default:?}, tail: {tail:?}");
                SExpr::Op(Op::DefaultTo(DefaultToDef {
                    default, tail: Box::new(tail)
                }))
            });

        default_to
    })
}

pub fn top_level_parser<'tokens, 'src: 'tokens, I>() -> 
impl Parser<'tokens, I, Vec<SExpr>, extra::Err<Rich<'tokens, Token, Span>>> 
where 
    I: ValueInput<'tokens, Token = Token, Span = SimpleSpan>
{
    let ident = select! { 
        Token::Identifier(ident) => ident 
    }.labelled("identifier");

    let ty = select! {
        Token::Int => Type::Int,
        Token::UInt => Type::UInt,
        Token::Principal => Type::Principal
    }.labelled("type");

    let func_visibility = select! {
        Token::OpDefinePublic => FunctionKind::Public,
        Token::OpDefinePrivate => FunctionKind::Private,
        Token::OpDefineReadOnly => FunctionKind::ReadOnly
    }.labelled("function definition");

    // Parses a single function argument in the format `(<name> <type>)`.
    let func_typedef = ident
        .then(ty)
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|(name, ty)| {
            eprintln!("func_typedef: {name}->{ty:?}");
            FuncArg { name, ty }
        });

    // Parses a function's signature in the format `(<name> (arg1 ty1) (arg2 ty2) ...)`.
    let func_signature = ident
        .then(func_typedef.repeated().collect::<Vec<_>>())
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|(name, args)| {
            eprintln!("func_signature: {name}->{args:?}");
            FuncSignature { name, args }
        });

    let define_fn = func_visibility
        .then(func_signature)
        .then(
            expr_parser()
        )
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|(kind, sig)| {
            eprintln!("define_fn: {kind:?}->{sig:?}");
            todo!()
        });

    // Parses `define-map` syntax.
    let define_map = just(Token::OpDefineMap) 
        .ignore_then(ident)
        .then(ty.labelled("key-type"))
        .then(ty.labelled("value-type"))
        .delimited_by(just(Token::ParenOpen), just(Token::ParenClose))
        .map(|((name, key_ty), val_ty)| {
            eprintln!("define-map {} {:?} {:?}", name, key_ty, val_ty);
            SExpr::Define(Define::Map(MapDef { name, key_ty, val_ty }))
        });

    define_map
        .or(define_fn)
        .repeated()
        .collect::<Vec<_>>()
}