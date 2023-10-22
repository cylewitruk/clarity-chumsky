use crate::types::{ClarityInteger, RefinedInteger};

/// Clarity expression types.
#[derive(Debug, Clone, PartialEq)]
pub enum SExpr<'a> {
    Error,

    Identifier(Box<Identifier<'a>>),
    Closure(Vec<Self>),
    Define(Define<'a>),
    Op(Op<'a>),
    TypeDef(Type<'a>),
    Literal(Literal<'a>),
    Keyword(Keyword),
    Tuple(Vec<ArgDef<'a>>),
}

/// Clarity keywords.
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

/// Clarity `define` statements.
#[derive(Debug, Clone, PartialEq)]
pub enum Define<'a> {
    Map(MapDef<'a>),
    DataVar,
    PublicFunction(Box<FuncDef<'a>>),
    PrivateFunction(Box<FuncDef<'a>>),
    ReadOnlyFunction(Box<FuncDef<'a>>),
    Tuple(TupleDef<'a>),
}

/// Clarity operations (functions).
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

/// Clarity literals.
#[derive(Debug, Clone, PartialEq)]
pub enum Literal<'a> {
    Int(i128),
    UInt(u128),
    Integer(ClarityInteger),
    AsciiString(&'a str),
    Utf8String(&'a str),
    Principal(&'a str),
}

/// Clarity type definitions.
#[derive(Debug, Clone, PartialEq)]
pub enum Type<'a> {
    Int,
    UInt,
    Bool,
    Principal,
    Buffer(u32),
    StringAscii(u32),
    StringUtf8(u32),
    List(u32, Box<SExpr<'a>>),
    Optional,
    Response,
    RefinedInteger(RefinedInteger),
}

/// Clarity identifiers.
#[derive(Debug, Clone, PartialEq)]
pub enum Identifier<'a> {
    String(&'a str),
    Expr(SExpr<'a>),
}

/// Clarity map definition.
#[derive(Debug, Clone, PartialEq)]
pub struct MapDef<'a> {
    pub name: &'a str,
    pub key_ty: Box<SExpr<'a>>,
    pub val_ty: Box<SExpr<'a>>,
}

/// Clarity function definition.
#[derive(Debug, Clone, PartialEq)]
pub struct FuncDef<'a> {
    pub signature: FuncSignature<'a>,
    pub body: SExpr<'a>,
}

/// Clarity function kind (visibility).
#[derive(Debug, Clone, PartialEq)]
pub enum FuncKind {
    Public,
    Private,
    ReadOnly,
}

/// Clarity function signature (name and arguments, without the body).
#[derive(Debug, Clone, PartialEq)]
pub struct FuncSignature<'a> {
    pub name: &'a str,
    pub args: Vec<ArgDef<'a>>,
}

/// Clarity argument definition (name + type).
#[derive(Debug, Clone, PartialEq)]
pub struct ArgDef<'a> {
    pub name: &'a str,
    pub ty: SExpr<'a>,
}

/// `default-to` definition.
#[derive(Debug, Clone, PartialEq)]
pub struct DefaultToDef<'a> {
    pub default: Box<SExpr<'a>>,
    pub tail: Box<SExpr<'a>>,
}

/// `tuple` definition.
#[derive(Debug, Clone, PartialEq)]
pub struct TupleDef<'a> {
    pub name: &'a str,
    pub args: Vec<ArgDef<'a>>,
}
