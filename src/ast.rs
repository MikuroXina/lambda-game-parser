use std::collections::HashMap;

use anyhow::{Context, Result, anyhow};
use nom::{
    IResult, Parser,
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, multispace0, multispace1},
    combinator::{fail, map, recognize},
    multi::{many0, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, terminated},
};
use nom_language::precedence::{Assoc, Operation, binary_op, precedence};

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

#[derive(Default)]
pub struct Env<'a> {
    assumptions: HashMap<AssumptionId<'a>, Assumption<'a>>,
    type_by_var: HashMap<VarId<'a>, Vec<Type<'a>>>,
}

impl std::fmt::Debug for Env<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Env")
            .field("assumptions", &self.assumptions)
            .finish()
    }
}

impl<'a> Env<'a> {
    fn from(list: Vec<Assumption<'a>>) -> Self {
        let mut assumptions = HashMap::new();
        let mut type_by_var = HashMap::new();
        for item in list {
            assumptions.insert(item.0.clone(), item.clone());
            type_by_var
                .entry(item.1)
                .or_insert_with(Vec::new)
                .push(item.2);
        }
        Self {
            assumptions,
            type_by_var,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct Assumption<'a>(AssumptionId<'a>, VarId<'a>, Type<'a>);

impl std::fmt::Debug for Assumption<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Assumption({:?} :: {:?} : {:?})", self.0, self.1, self.2)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct AssumptionId<'a>(&'a str);
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct VarId<'a>(&'a str);
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TypeVarId<'a>(&'a str);

struct Derivation<'a> {
    target: Target<'a>,
    proof: Proof<'a>,
}

impl std::fmt::Debug for Derivation<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} by {:?}", self.target, self.proof)
    }
}

struct Target<'a>(VarId<'a>, Type<'a>);

impl std::fmt::Debug for Target<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} : {:?}", self.0, self.1)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum Type<'a> {
    Var(TypeVarId<'a>),
    Product(Box<Type<'a>>, Box<Type<'a>>),
    Sum(Box<Type<'a>>, Box<Type<'a>>),
    Func(Box<Type<'a>>, Box<Type<'a>>),
    Placeholder,
}

impl std::fmt::Debug for Type<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Var(id) => f.debug_tuple("Var").field(id).finish(),
            Self::Product(lhs, rhs) => write!(f, "{lhs:?} × {rhs:?}"),
            Self::Sum(lhs, rhs) => write!(f, "{lhs:?} + {rhs:?}"),
            Self::Func(lhs, rhs) => write!(f, "{lhs:?} -> {rhs:?}"),
            Self::Placeholder => write!(f, "Placeholder"),
        }
    }
}

enum Expression<'a> {
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

#[derive(Debug)]
enum Proof<'a> {
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
            binary_op(4, Assoc::Left, tag("×")),
            binary_op(3, Assoc::Left, tag("+")),
            binary_op(2, Assoc::Right, tag("->")),
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
    let (i, left_case) =
        preceded((multispace0, tag(","), multispace0), parse_expression).parse(i)?;
    let (i, right_case) = delimited(
        (multispace0, tag(","), multispace0),
        parse_expression,
        (multispace0, tag(")"), multispace0),
    )
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
    let (i, var) = terminated(parse_var_id, (multispace0, tag(":"), multispace0)).parse(i)?;
    let (i, ty) = parse_type(i)?;
    Ok((i, (var, ty)))
}

fn parse_lambda(i: &str) -> IResult<&str, Expression> {
    let (i, (id, ty)) = preceded((tag("lambda"), multispace1), parse_var_decl).parse(i)?;
    let (i, body) = preceded((multispace0, tag("."), multispace1), parse_expression).parse(i)?;
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
    let (i, func) = parse_expression(i)?;
    let (i, argument) = delimited(
        (multispace0, tag("("), multispace0),
        parse_expression,
        (multispace0, tag(")"), multispace0),
    )
    .parse(i)?;
    Ok((
        i,
        Expression::Apply {
            func: func.into(),
            argument: argument.into(),
        },
    ))
}

fn parse_expression(i: &str) -> IResult<&str, Expression> {
    alt((
        map(parse_var_id, |id| Expression::Var(id)),
        parse_pair,
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
    ))
    .parse(i)
}

fn parse_proof(i: &str) -> IResult<&str, Proof> {
    alt((
        map(
            delimited(
                (tag("var"), multispace1, tag("{"), multispace0),
                parse_assumption_id,
                (multispace0, tag("}"), multispace0),
            ),
            |id| Proof::Var { using: id },
        ),
        map(
            delimited(
                (tag("pair"), multispace1, tag("{"), multispace0),
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
                (tag("left"), multispace1, tag("{"), multispace0),
                parse_derivation,
                (multispace0, tag("}"), multispace0),
            ),
            |derivation| Proof::Left(derivation.into()),
        ),
        map(
            delimited(
                (tag("right"), multispace1, tag("{"), multispace0),
                parse_derivation,
                (multispace0, tag("}"), multispace0),
            ),
            |derivation| Proof::Right(derivation.into()),
        ),
        map(
            delimited(
                (tag("inl"), multispace1, tag("{"), multispace0),
                parse_derivation,
                (multispace0, tag("}"), multispace0),
            ),
            |derivation| Proof::InL(derivation.into()),
        ),
        map(
            delimited(
                (tag("inr"), multispace1, tag("{"), multispace0),
                parse_derivation,
                (multispace0, tag("}"), multispace0),
            ),
            |derivation| Proof::InR(derivation.into()),
        ),
        map(
            delimited(
                (tag("case"), multispace1, tag("{"), multispace0),
                (
                    terminated(parse_derivation, (multispace0, tag(";"), multispace0)),
                    parse_assumption,
                    delimited(
                        (multispace0, tag("["), multispace0),
                        terminated(parse_derivation, (multispace0, tag(";"), multispace0)),
                        (multispace0, tag("]"), multispace0),
                    ),
                    parse_assumption,
                    delimited(
                        (multispace0, tag("["), multispace0),
                        terminated(parse_derivation, (multispace0, tag(";"), multispace0)),
                        (multispace0, tag("]"), multispace0),
                    ),
                ),
                (multispace0, tag("}"), multispace0),
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

fn parse_derivation(i: &str) -> IResult<&str, Derivation> {
    let (i, (var_id, ty)) =
        terminated(parse_var_decl, (multispace1, tag("by"), multispace1)).parse(i)?;
    let (i, proof) = terminated(parse_proof, multispace0).parse(i)?;
    Ok((
        i,
        Derivation {
            target: Target(var_id, ty),
            proof,
        },
    ))
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
    let (i, (var_id, ty)) =
        delimited((tag("|-"), multispace0), parse_var_decl, multispace0).parse(i)?;
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
            env: Env::from(assumptions),
            identifier,
            target: Target(var_id, ty),
            body,
        },
    ))
}
