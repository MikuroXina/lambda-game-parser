use anyhow::{Context, Result, anyhow};
use nom::{
    IResult, Parser,
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, multispace0, multispace1},
    combinator::{cut, fail, map, recognize},
    multi::{many0, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair, terminated},
};
use nom_language::precedence::{Assoc, Operation, binary_op, precedence};

use crate::pad_adapter::PadAdapter;

#[derive(Debug)]
pub struct LambdaGame<'a> {
    answers: Vec<Answer<'a>>,
}

impl<'a> LambdaGame<'a> {
    pub fn from(program: &'a str) -> Result<Self> {
        let (_, answers) = separated_list1(multispace0, parse_answer)
            .parse_complete(program)
            .map_err(|err| anyhow!("{err:#?}"))
            .context("syntax error")?;
        Ok(Self { answers })
    }

    pub fn answers(&self) -> &[Answer] {
        &self.answers
    }
}

#[derive(Debug)]
pub struct Answer<'a> {
    env: Env<'a>,
    identifier: &'a str,
    target: Target<'a>,
    body: Derivation<'a>,
}

impl Answer<'_> {
    pub fn env(&self) -> &Env {
        &self.env
    }

    pub fn body(&self) -> &Derivation {
        &self.body
    }
}

#[derive(Debug, Default, Clone)]
pub struct Env<'a> {
    assumptions: Vec<Assumption<'a>>,
}

impl<'a> Env<'a> {
    pub fn assumptions(&self) -> impl Iterator<Item = &Assumption> {
        self.assumptions.iter()
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Assumption<'a>(AssumptionId<'a>, VarId<'a>, Type<'a>);

impl std::fmt::Debug for Assumption<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Assumption({:?} :: {:?} : {:?})", self.0, self.1, self.2)
    }
}

impl Assumption<'_> {
    pub fn id(&self) -> AssumptionId {
        self.0
    }

    pub fn var_id(&self) -> VarId {
        self.1
    }

    pub fn ty(&self) -> &Type {
        &self.2
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssumptionId<'a>(&'a str);

impl std::fmt::Debug for AssumptionId<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId<'a>(&'a str);

impl std::fmt::Debug for VarId<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeVarId<'a>(&'a str);

impl std::fmt::Debug for TypeVarId<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Derivation<'a> {
    target: Target<'a>,
    proof: Proof<'a>,
}

impl std::fmt::Debug for Derivation<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            write!(f, "{:#?} by {:#?}", self.target, self.proof)
        } else {
            write!(f, "{:?} by {:?}", self.target, self.proof)
        }
    }
}

impl Derivation<'_> {
    pub fn target(&self) -> &Target {
        &self.target
    }

    pub fn proof(&self) -> &Proof {
        &self.proof
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Target<'a>(Expression<'a>, Type<'a>);

impl std::fmt::Debug for Target<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} : {:?}", self.0, self.1)
    }
}

impl Target<'_> {
    pub fn expr(&self) -> &Expression {
        &self.0
    }

    pub fn ty(&self) -> &Type {
        &self.1
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Type<'a> {
    Var(TypeVarId<'a>),
    Product(Box<Type<'a>>, Box<Type<'a>>),
    Sum(Box<Type<'a>>, Box<Type<'a>>),
    Func(Box<Type<'a>>, Box<Type<'a>>),
    Placeholder,
}

impl std::fmt::Debug for Type<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Var(id) => write!(f, "{id:?}"),
            Self::Product(lhs, rhs) => write!(f, "{lhs:?} × {rhs:?}"),
            Self::Sum(lhs, rhs) => write!(f, "{lhs:?} + {rhs:?}"),
            Self::Func(lhs, rhs) => write!(f, "{lhs:?} -> {rhs:?}"),
            Self::Placeholder => write!(f, "Placeholder"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Expression<'a> {
    Var(VarId<'a>),
    Pair(Box<Expression<'a>>, Box<Expression<'a>>),
    Left(Box<Expression<'a>>),
    Right(Box<Expression<'a>>),
    InL(Box<Expression<'a>>),
    InR(Box<Expression<'a>>),
    Case {
        or: Box<Expression<'a>>,
        case_left: Box<Expression<'a>>,
        case_right: Box<Expression<'a>>,
    },
    Lambda {
        param_id: VarId<'a>,
        param_type: Type<'a>,
        body: Box<Expression<'a>>,
    },
    Apply {
        func: Box<Expression<'a>>,
        argument: Box<Expression<'a>>,
    },
}

impl std::fmt::Debug for Expression<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Var(id) => write!(f, "{id:?}"),
            Self::Pair(lhs, rhs) => f.debug_tuple("").field(lhs).field(rhs).finish(),
            Self::Left(expr) => f.debug_tuple("left").field(expr).finish(),
            Self::Right(expr) => f.debug_tuple("right").field(expr).finish(),
            Self::InL(expr) => f.debug_tuple("inl").field(expr).finish(),
            Self::InR(expr) => f.debug_tuple("inr").field(expr).finish(),
            Self::Case {
                or,
                case_left,
                case_right,
            } => f
                .debug_struct("case")
                .field("or", or)
                .field("case_left", case_left)
                .field("case_right", case_right)
                .finish(),
            Self::Lambda {
                param_id,
                param_type,
                body,
            } => write!(f, "lambda {param_id:?} : {param_type:?}. {body:?}"),
            Self::Apply { func, argument } => write!(f, "{func:?}({argument:?})"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Proof<'a> {
    Var {
        using: AssumptionId<'a>,
    },
    Pair {
        left: Box<Derivation<'a>>,
        right: Box<Derivation<'a>>,
    },
    Left(Box<Derivation<'a>>),
    Right(Box<Derivation<'a>>),
    InL(Box<Derivation<'a>>),
    InR(Box<Derivation<'a>>),
    Case {
        using_or: Box<Derivation<'a>>,
        left_param: Assumption<'a>,
        left_case: Box<Derivation<'a>>,
        right_param: Assumption<'a>,
        right_case: Box<Derivation<'a>>,
    },
    Lambda {
        argument_assumption: Assumption<'a>,
        body: Box<Derivation<'a>>,
    },
    Apply {
        func: Box<Derivation<'a>>,
        param: Box<Derivation<'a>>,
    },
}

impl std::fmt::Debug for Proof<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            use std::fmt::Write;
            let mut f = PadAdapter::new(f);
            match self {
                Proof::Var { using } => write!(
                    f,
                    r#"var {{
    {using:#?}
}}"#
                ),
                Proof::Pair { left, right } => write!(
                    f,
                    r#"pair {{
    {left:#?};
    {right:#?}
}}"#
                ),
                Proof::Left(de) => write!(
                    f,
                    r#"left {{
    {de:#?}
}}"#
                ),
                Proof::Right(de) => write!(
                    f,
                    r#"right {{
    {de:#?}
}}"#
                ),
                Proof::InL(de) => write!(
                    f,
                    r#"inl {{
    {de:#?}
}}"#
                ),
                Proof::InR(de) => write!(
                    f,
                    r#"inr {{
    {de:#?}
}}"#
                ),
                Proof::Case {
                    using_or,
                    left_param,
                    left_case,
                    right_param,
                    right_case,
                } => write!(
                    f,
                    r#"case {{
    {using_or:#?};
    {left_param:#?}[
        {left_case:#?}
    ];
    {right_param:#?}[
        {right_case:#?}
    ];
}}"#
                ),
                Proof::Lambda {
                    argument_assumption,
                    body,
                } => write!(
                    f,
                    r#"lambda {{
    {argument_assumption:#?}[
        {body:#?}
    ];
}}"#
                ),
                Proof::Apply { func, param } => write!(
                    f,
                    r#"apply {{
    {func:#?};
    {param:#?}
}}"#
                ),
            }
        } else {
            match self {
                Self::Var { using } => write!(f, "var {{ {using:?} }}"),
                Self::Pair { left, right } => write!(f, "pair {{ {left:?}, {right:?} }}"),
                Self::Left(expr) => write!(f, "left {{ {expr:?} }}"),
                Self::Right(expr) => write!(f, "right {{ {expr:?} }}"),
                Self::InL(expr) => write!(f, "inl {{ {expr:?} }}"),
                Self::InR(expr) => write!(f, "inr {{ {expr:?} }}"),
                Self::Case {
                    using_or,
                    left_param,
                    left_case,
                    right_param,
                    right_case,
                } => write!(
                    f,
                    "case {{ {using_or:?}; {left_param:?} [ {left_case:?} ]; {right_param:?} [ {right_case:?} ]; }}"
                ),
                Self::Lambda {
                    argument_assumption,
                    body,
                } => write!(f, "lambda {{ {argument_assumption:?} [ {body:?} ]; }}"),
                Self::Apply { func, param } => write!(f, "apply {{ {func:?}; {param:?} }}"),
            }
        }
    }
}

fn parse_assumption(i: &str) -> IResult<&str, Assumption> {
    let (i, assumption_id) =
        terminated(parse_assumption_id, (multispace0, tag("::"), multispace0)).parse(i)?;
    let (i, (var_id, ty)) = terminated(parse_var_decl, multispace0).parse(i)?;
    Ok((i, Assumption(assumption_id, var_id, ty)))
}

fn parse_assumption_id(i: &str) -> IResult<&str, AssumptionId> {
    map(recognize(pair(alpha1, many0(alphanumeric1))), AssumptionId).parse(i)
}

fn parse_type_var(i: &str) -> IResult<&str, Type> {
    map(recognize(pair(alpha1, many0(alphanumeric1))), |id| {
        Type::Var(TypeVarId(id))
    })
    .parse(i)
}

fn parse_type(i: &str) -> IResult<&str, Type> {
    precedence(
        fail(),
        fail(),
        alt((
            binary_op(
                4,
                Assoc::Left,
                delimited(multispace0, tag("×"), multispace0),
            ),
            binary_op(
                3,
                Assoc::Left,
                delimited(multispace0, tag("+"), multispace0),
            ),
            binary_op(
                2,
                Assoc::Right,
                delimited(multispace0, tag("->"), multispace0),
            ),
        )),
        parse_type_var,
        |op: Operation<&str, &str, &str, Type>| match op {
            Operation::Binary(lhs, "×", rhs) => Ok(Type::Product(lhs.into(), rhs.into())),
            Operation::Binary(lhs, "+", rhs) => Ok(Type::Sum(lhs.into(), rhs.into())),
            Operation::Binary(lhs, "->", rhs) => Ok(Type::Func(lhs.into(), rhs.into())),
            _ => Err("Invalid combination"),
        },
    )(i)
}

fn parse_var_id(i: &str) -> IResult<&str, VarId> {
    map(recognize((alpha1, many0(alphanumeric1))), VarId).parse(i)
}

fn parse_pair(i: &str) -> IResult<&str, Expression> {
    let (i, left) = preceded((tag("<"), multispace0), parse_expression).parse(i)?;
    let (i, right) = delimited(
        (multispace0, tag(","), multispace0),
        parse_expression,
        (multispace0, tag(">"), multispace0),
    )
    .parse(i)?;
    Ok((i, Expression::Pair(left.into(), right.into())))
}

fn parse_case(i: &str) -> IResult<&str, Expression> {
    let (i, or) = preceded((tag("case("), multispace0), parse_expression).parse(i)?;
    let (i, left_case) = cut(preceded(
        (multispace0, tag(","), multispace0),
        parse_expression,
    ))
    .parse(i)?;
    let (i, right_case) = cut(delimited(
        (multispace0, tag(","), multispace0),
        parse_expression,
        (multispace0, tag(")"), multispace0),
    ))
    .parse(i)?;
    Ok((
        i,
        Expression::Case {
            or: or.into(),
            case_left: left_case.into(),
            case_right: right_case.into(),
        },
    ))
}

fn parse_var_decl(i: &str) -> IResult<&str, (VarId, Type)> {
    separated_pair(
        parse_var_id,
        (multispace0, tag(":"), multispace0),
        parse_type,
    )
    .parse(i)
}

fn parse_lambda(i: &str) -> IResult<&str, Expression> {
    let (i, (id, ty)) = preceded((tag("lambda"), multispace1), parse_var_decl).parse(i)?;
    let (i, body) = cut(preceded(
        (multispace0, tag("."), multispace1),
        parse_expression,
    ))
    .parse(i)?;
    Ok((
        i,
        Expression::Lambda {
            param_id: id,
            param_type: ty,
            body: body.into(),
        },
    ))
}

fn parse_apply(i: &str) -> IResult<&str, Expression> {
    let (i, func) = terminated(parse_var_id, (multispace0, tag("("), multispace0)).parse(i)?;
    let (i, argument) =
        terminated(parse_expression, (multispace0, tag(")"), multispace0)).parse(i)?;
    Ok((
        i,
        Expression::Apply {
            func: Expression::Var(func).into(),
            argument: argument.into(),
        },
    ))
}

fn parse_expression(i: &str) -> IResult<&str, Expression> {
    alt((
        map(
            delimited(
                (tag("left("), multispace0),
                parse_expression,
                (multispace0, tag(")"), multispace0),
            ),
            |expr| Expression::Left(expr.into()),
        ),
        map(
            delimited(
                (tag("right("), multispace0),
                parse_expression,
                (multispace0, tag(")"), multispace0),
            ),
            |expr| Expression::Right(expr.into()),
        ),
        map(
            delimited(
                (tag("inl("), multispace0),
                parse_expression,
                (multispace0, tag(")"), multispace0),
            ),
            |expr| Expression::InL(expr.into()),
        ),
        map(
            delimited(
                (tag("inr("), multispace0),
                parse_expression,
                (multispace0, tag(")"), multispace0),
            ),
            |expr| Expression::InR(expr.into()),
        ),
        parse_case,
        parse_lambda,
        parse_apply,
        parse_pair,
        map(parse_var_id, |id| Expression::Var(id)),
    ))
    .parse(i)
}

fn parse_proof(i: &str) -> IResult<&str, Proof> {
    alt((
        map(
            delimited(
                (tag("var"), multispace0, tag("{"), multispace0),
                parse_assumption_id,
                (multispace0, tag("}"), multispace0),
            ),
            |id| Proof::Var { using: id },
        ),
        map(
            delimited(
                (tag("pair"), multispace0, tag("{"), multispace0),
                (
                    terminated(parse_derivation, (multispace0, tag(";"), multispace0)),
                    parse_derivation,
                ),
                (multispace0, tag("}"), multispace0),
            ),
            |(left, right)| Proof::Pair {
                left: left.into(),
                right: right.into(),
            },
        ),
        map(
            delimited(
                (tag("left"), multispace0, tag("{"), multispace0),
                parse_derivation,
                (multispace0, tag("}"), multispace0),
            ),
            |derivation| Proof::Left(derivation.into()),
        ),
        map(
            delimited(
                (tag("right"), multispace0, tag("{"), multispace0),
                parse_derivation,
                (multispace0, tag("}"), multispace0),
            ),
            |derivation| Proof::Right(derivation.into()),
        ),
        map(
            delimited(
                (tag("inl"), multispace0, tag("{"), multispace0),
                parse_derivation,
                (multispace0, tag("}"), multispace0),
            ),
            |derivation| Proof::InL(derivation.into()),
        ),
        map(
            delimited(
                (tag("inr"), multispace0, tag("{"), multispace0),
                parse_derivation,
                (multispace0, tag("}"), multispace0),
            ),
            |derivation| Proof::InR(derivation.into()),
        ),
        map(
            delimited(
                (tag("case"), multispace0, tag("{"), multispace0),
                (
                    terminated(parse_derivation, (multispace0, tag(";"), multispace0)),
                    parse_assumption,
                    delimited(
                        (multispace0, tag("["), multispace0),
                        parse_derivation,
                        (multispace0, tag("]"), multispace0, tag(";"), multispace0),
                    ),
                    parse_assumption,
                    delimited(
                        (multispace0, tag("["), multispace0),
                        parse_derivation,
                        (multispace0, tag("]"), multispace0, tag(";"), multispace0),
                    ),
                ),
                (tag("}"), multispace0),
            ),
            |(using_or, left_param, left_case, right_param, right_case)| Proof::Case {
                using_or: using_or.into(),
                left_param,
                left_case: left_case.into(),
                right_param,
                right_case: right_case.into(),
            },
        ),
        map(
            delimited(
                (tag("lambda"), multispace1, tag("{"), multispace0),
                (
                    parse_assumption,
                    delimited(
                        (multispace0, tag("["), multispace0),
                        terminated(parse_derivation, (multispace0, tag(";"), multispace0)),
                        (multispace0, tag("]"), multispace0),
                    ),
                ),
                (multispace0, tag("}"), multispace0),
            ),
            |(argument_assumption, body)| Proof::Lambda {
                argument_assumption,
                body: body.into(),
            },
        ),
        map(
            delimited(
                (tag("apply"), multispace1, tag("{"), multispace0),
                (
                    terminated(parse_derivation, (multispace0, tag(";"), multispace0)),
                    terminated(parse_derivation, multispace0),
                ),
                (multispace0, tag("}"), multispace0),
            ),
            |(func, param)| Proof::Apply {
                func: func.into(),
                param: param.into(),
            },
        ),
    ))
    .parse(i)
}

fn parse_target(i: &str) -> IResult<&str, Target> {
    let (i, expr) = terminated(parse_expression, (multispace0, tag(":"), multispace0)).parse(i)?;
    let (i, ty) = terminated(parse_type, multispace1).parse(i)?;
    Ok((i, Target(expr, ty)))
}

fn parse_derivation(i: &str) -> IResult<&str, Derivation> {
    let (i, target) = terminated(parse_target, (tag("by"), multispace0)).parse(i)?;
    let (i, proof) = terminated(parse_proof, multispace0).parse(i)?;
    Ok((i, Derivation { target, proof }))
}

fn parse_assumptions(i: &str) -> IResult<&str, Vec<Assumption>> {
    separated_list0(
        (tag(","), multispace0),
        terminated(parse_assumption, multispace0),
    )
    .parse(i)
}

fn parse_answer(i: &str) -> IResult<&str, Answer> {
    let (i, identifier) = delimited(
        (tag("A"), multispace0, tag("["), multispace0),
        alphanumeric1,
        (multispace0, tag("]"), multispace0, tag("["), multispace0),
    )
    .parse(i)?;
    let (i, assumptions) = parse_assumptions(i)?;
    let (i, target) = delimited((tag("|-"), multispace0), parse_target, multispace0).parse(i)?;
    let (i, body) = delimited(
        (
            tag("in"),
            multispace0,
            tag("Lambda"),
            multispace0,
            tag("since"),
            multispace0,
        ),
        parse_derivation,
        (multispace0, tag("]"), multispace0),
    )
    .parse(i)?;
    Ok((
        i,
        Answer {
            env: Env { assumptions },
            identifier,
            target,
            body,
        },
    ))
}
