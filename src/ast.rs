use crate::types::{ClarityInteger, RefinedInteger};

#[derive(Debug, Clone, PartialEq)]
pub enum SExpr<'a> {
    Error,

    Identifier(Box<Identifier<'a>>),
    RefinedInteger(RefinedInteger),
    Closure(Vec<Self>),
    Define(Define<'a>),
    Op(Op<'a>),
    TypeDef(Type),
    Literal(Literal<'a>),
    Keyword(Keyword),
    Tuple(Vec<ArgDef<'a>>)
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Keyword {
    BlockHeight,
    BurnBlockHeight,
    ChainId,
    ContractCaller,
    False,
    IsInMainnet,
    IsInRegTest,
    None,
    StxLiquidSupply,
    True,
    TxSender,
    TxSponsor,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Define<'a> {
    Map(MapDef<'a>),
    DataVar,
    PublicFunction(Box<FuncDef<'a>>),
    PrivateFunction(Box<FuncDef<'a>>),
    ReadOnlyFunction(Box<FuncDef<'a>>),
    Tuple(TupleDef<'a>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Op<'a> {
    Add,
    Sub,
    Mul,
    Div,
    DefaultTo(DefaultToDef<'a>),
    MapGet,
    Ok(Box<SExpr<'a>>),
    Err(Box<SExpr<'a>>),
    MapSet,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal<'a> {
    Int(i128),
    UInt(u128),
    Integer(ClarityInteger),
    AsciiString(&'a str),
    Utf8String(&'a str),
    Principal(&'a str)
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    UInt,
    Bool,
    Principal,
    Buff,
    StringAscii(u32),
    StringUtf8(u32),
    List,
    Optional,
    Response,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Identifier<'a> {
    String(&'a str),
    Expr(SExpr<'a>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct MapDef<'a> {
    pub name: &'a str,
    pub key_ty: Box<SExpr<'a>>,
    pub val_ty: Box<SExpr<'a>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncDef<'a> {
    pub signature: FuncSignature<'a>,
    pub body: SExpr<'a>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum FuncKind {
    Public,
    Private,
    ReadOnly,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncSignature<'a> {
    pub name: &'a str,
    pub args: Vec<ArgDef<'a>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArgDef<'a> {
    pub name: &'a str,
    pub ty: SExpr<'a>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DefaultToDef<'a> {
    pub default: Box<SExpr<'a>>,
    pub tail: Box<SExpr<'a>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TupleDef<'a> {
    pub name: &'a str,
    pub args: Vec<ArgDef<'a>>,
}
