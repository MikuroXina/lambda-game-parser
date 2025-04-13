use std::collections::HashMap;

use thiserror::Error;

use crate::ast::{
    Answer, Assumption, AssumptionId, Env, Expression, LambdaGame, Proof, Target, Type, VarId,
};

#[derive(Debug, Error)]
pub enum VerificationError<'a> {
    #[error("assumption id {0:?} is duplicated")]
    DuplicatedAssumptionId(AssumptionId<'a>),
    #[error("assumption by id {0:?} is not found")]
    AssumptionNotFound(AssumptionId<'a>),
    #[error("variable by id {0:?} is not found")]
    VariableNotFound(VarId<'a>),
    #[error("expected target type {expected:?}, but found {actual:?}")]
    MismatchedTargetType {
        expected: Type<'a>,
        actual: Type<'a>,
    },
    #[error("expected expression {expr:?} has type {expected_type:?}")]
    MismatchedType {
        expr: Expression<'a>,
        expected_type: Type<'a>,
    },
    #[error("expected expression {0}")]
    ExpectedExpression(&'static str),
    #[error("expected type {0}")]
    ExpectedType(&'static str),
}

pub fn verify<'a>(game: &'a LambdaGame) -> Result<(), VerificationError<'a>> {
    for answer in game.answers() {
        verify_answer(answer)?;
    }
    Ok(())
}

fn verify_answer<'a>(answer: &'a Answer) -> Result<(), VerificationError<'a>> {
    let target = answer.body().target();
    let proof = answer.body().proof();
    verify_proof(&mut ProofContext::from_env(answer.env())?, target, proof)?;
    Ok(())
}

fn verify_proof<'a>(
    env: &mut ProofContext<'a>,
    target: &'a Target,
    proof: &'a Proof,
) -> Result<(), VerificationError<'a>> {
    match proof {
        Proof::Var { using } => {
            let assume = env
                .get(using)
                .ok_or_else(|| VerificationError::AssumptionNotFound(*using))?;
            verify_match_type(target.ty(), assume.ty())?;
        }
        Proof::Pair { left, right } => {
            verify_proof(env, left.target(), left.proof())?;
            verify_proof(env, right.target(), right.proof())?;
            let expected = Type::Product(
                left.target().ty().clone().into(),
                right.target().ty().clone().into(),
            );
            verify_match_type(&expected, target.ty())?;
            let Expression::Pair(left_expr, right_expr) = target.expr() else {
                return Err(VerificationError::MismatchedType {
                    expr: target.expr().clone(),
                    expected_type: expected,
                });
            };
            verify_expr_has_type(env, left_expr, left.target().ty())?;
            verify_expr_has_type(env, right_expr, right.target().ty())?;
        }
        Proof::Left(derivation) => {
            verify_proof(env, derivation.target(), derivation.proof())?;
            let Type::Product(left_ty, _) = derivation.target().ty() else {
                return Err(VerificationError::MismatchedTargetType {
                    expected: Type::Product(target.ty().clone().into(), Type::Placeholder.into()),
                    actual: derivation.target().ty().clone(),
                });
            };
            let Expression::Left(tuple_expr) = target.expr() else {
                return Err(VerificationError::ExpectedExpression("left"));
            };
            verify_expr_has_type(env, tuple_expr, derivation.target().ty())?;
            verify_match_type(target.ty(), left_ty.as_ref())?;
        }
        Proof::Right(derivation) => {
            verify_proof(env, derivation.target(), derivation.proof())?;
            let Type::Product(_, right_ty) = derivation.target().ty() else {
                return Err(VerificationError::MismatchedTargetType {
                    expected: Type::Product(Type::Placeholder.into(), target.ty().clone().into()),
                    actual: derivation.target().ty().clone(),
                });
            };
            let Expression::Right(tuple_expr) = target.expr() else {
                return Err(VerificationError::ExpectedExpression("right"));
            };
            verify_expr_has_type(env, tuple_expr, derivation.target().ty())?;
            verify_match_type(target.ty(), right_ty.as_ref())?;
        }
        Proof::InL(derivation) => {
            verify_proof(env, derivation.target(), derivation.proof())?;
            let target_out_ty = derivation.target().ty();
            let Type::Sum(left_ty, _) = target.ty() else {
                return Err(VerificationError::MismatchedTargetType {
                    expected: Type::Sum(target_out_ty.clone().into(), Type::Placeholder.into()),
                    actual: target.ty().clone(),
                });
            };
            if &*target_out_ty != &**left_ty {
                return Err(VerificationError::MismatchedType {
                    expr: derivation.target().expr().clone(),
                    expected_type: *left_ty.clone(),
                });
            }
            let Expression::InL(left_expr) = target.expr() else {
                return Err(VerificationError::MismatchedType {
                    expr: target.expr().clone(),
                    expected_type: *left_ty.clone(),
                });
            };
            verify_expr_has_type(env, left_expr, left_ty)?;
        }
        Proof::InR(derivation) => {
            verify_proof(env, derivation.target(), derivation.proof())?;
            let target_out_ty = derivation.target().ty();
            let Type::Sum(_, right_ty) = target.ty() else {
                return Err(VerificationError::MismatchedTargetType {
                    expected: Type::Sum(Type::Placeholder.into(), target_out_ty.clone().into()),
                    actual: target.ty().clone(),
                });
            };
            if target_out_ty != right_ty.as_ref() {
                return Err(VerificationError::MismatchedType {
                    expr: derivation.target().expr().clone(),
                    expected_type: *right_ty.clone(),
                });
            }
            let Expression::InR(right_expr) = target.expr() else {
                return Err(VerificationError::MismatchedType {
                    expr: target.expr().clone(),
                    expected_type: *right_ty.clone(),
                });
            };
            verify_expr_has_type(env, right_expr, right_ty)?;
        }
        Proof::Case {
            using_or,
            left_param,
            left_case,
            right_param,
            right_case,
        } => {
            verify_proof(env, using_or.target(), using_or.proof())?;
            let Type::Sum(left_ty, right_ty) = using_or.target().ty() else {
                return Err(VerificationError::MismatchedType {
                    expr: using_or.target().expr().clone(),
                    expected_type: Type::Sum(Type::Placeholder.into(), Type::Placeholder.into()),
                });
            };
            verify_match_type(&left_ty, left_param.ty())?;
            verify_match_type(&right_ty, right_param.ty())?;
            verify_match_type(target.ty(), left_case.target().ty())?;
            verify_match_type(target.ty(), right_case.target().ty())?;
            env.push(left_param);
            verify_proof(env, left_case.target(), left_case.proof())?;
            env.pop(&left_param.id());
            env.push(right_param);
            verify_proof(env, right_case.target(), right_case.proof())?;
            env.pop(&right_param.id());
        }
        Proof::Lambda {
            argument_assumption,
            body,
        } => {
            let Expression::Lambda {
                param_type: lambda_param_type,
                body: lambda_body,
                ..
            } = target.expr()
            else {
                return Err(VerificationError::ExpectedExpression("lambda"));
            };
            verify_match_type(lambda_param_type, argument_assumption.ty())?;
            verify_match_type(&find_expr_type(env, lambda_body)?, body.target().ty())?;
            env.push(argument_assumption);
            verify_proof(env, body.target(), body.proof())?;
            env.pop(&argument_assumption.id());
        }
        Proof::Apply { func, param } => {
            let param_ty = param.target().ty();
            let Type::Func(func_param, func_ret) = func.target().ty() else {
                return Err(VerificationError::ExpectedExpression(
                    "function application",
                ));
            };
            verify_match_type(func_param, param_ty)?;
            verify_match_type(target.ty(), func_ret)?;
        }
    }
    Ok(())
}

fn verify_expr_has_type<'a>(
    env: &mut ProofContext<'a>,
    expr: &Expression<'a>,
    ty: &Type<'a>,
) -> Result<(), VerificationError<'a>> {
    match expr {
        Expression::Var(var_id) => {
            let env_var_ty = env
                .get_var_type(var_id)
                .ok_or_else(|| VerificationError::VariableNotFound(var_id.clone()))?;
            verify_match_type(ty, env_var_ty)?;
        }
        Expression::Pair(lhs, rhs) => {
            let Type::Product(lhs_ty, rhs_ty) = ty else {
                return Err(VerificationError::MismatchedType {
                    expr: expr.clone(),
                    expected_type: Type::Product(
                        Type::Placeholder.into(),
                        Type::Placeholder.into(),
                    ),
                });
            };
            verify_expr_has_type(env, &lhs, &lhs_ty)?;
            verify_expr_has_type(env, &rhs, &rhs_ty)?;
        }
        Expression::Left(expr) => {
            verify_expr_has_type(
                env,
                expr,
                &Type::Product(ty.clone().into(), Type::Placeholder.into()),
            )?;
        }
        Expression::Right(expr) => {
            verify_expr_has_type(
                env,
                expr,
                &Type::Product(Type::Placeholder.into(), ty.clone().into()),
            )?;
        }
        Expression::InL(expr) => {
            let Type::Sum(left_ty, _) = ty else {
                return Err(VerificationError::ExpectedType("Sum"));
            };
            verify_expr_has_type(env, expr, left_ty)?;
        }
        Expression::InR(expr) => {
            let Type::Sum(_, right_ty) = ty else {
                return Err(VerificationError::ExpectedType("Sum"));
            };
            verify_expr_has_type(env, expr, right_ty)?;
        }
        Expression::Case {
            or,
            case_left,
            case_right,
        } => {
            let Type::Sum(left_ty, right_ty) = find_expr_type(env, or)? else {
                return Err(VerificationError::ExpectedType("Sum"));
            };
            let Expression::Lambda {
                param_type: left_param_type,
                body: left_body,
                ..
            } = case_left.as_ref()
            else {
                return Err(VerificationError::ExpectedExpression("lambda"));
            };
            if left_ty.as_ref() != left_param_type {
                return Err(VerificationError::MismatchedType {
                    expr: *case_left.clone(),
                    expected_type: Type::Func(left_ty, Type::Placeholder.into()),
                });
            }
            verify_match_type(ty, &find_expr_type(env, left_body)?)?;
            let Expression::Lambda {
                param_type: right_param_type,
                body: right_body,
                ..
            } = case_right.as_ref()
            else {
                return Err(VerificationError::ExpectedExpression("lambda"));
            };
            if right_ty.as_ref() != right_param_type {
                return Err(VerificationError::MismatchedType {
                    expr: *case_right.clone(),
                    expected_type: Type::Func(right_ty, Type::Placeholder.into()),
                });
            }
            verify_match_type(ty, &find_expr_type(env, right_body)?)?;
        }
        Expression::Lambda {
            param_type, body, ..
        } => {
            let body_ty = find_expr_type(env, body)?;
            let Type::Func(param_ty, body_ty) = ty else {
                return Err(VerificationError::MismatchedType {
                    expr: expr.clone(),
                    expected_type: Type::Func(Type::Placeholder.into(), body_ty.into()),
                });
            };
            verify_match_type(param_ty, param_type)?;
            verify_match_type(body_ty, &find_expr_type(env, body)?)?;
        }
        Expression::Apply { func, argument } => {
            let Expression::Lambda {
                param_type, body, ..
            } = func.as_ref()
            else {
                return Err(VerificationError::ExpectedExpression("lambda"));
            };
            verify_match_type(param_type, &find_expr_type(env, argument)?)?;
            verify_match_type(ty, &find_expr_type(env, body)?)?;
        }
    }
    Ok(())
}

fn verify_match_type<'a>(
    expected: &Type<'a>,
    actual: &Type<'a>,
) -> Result<(), VerificationError<'a>> {
    match (expected, actual) {
        (Type::Product(expected_l, expected_r), Type::Product(actual_l, actual_r))
            if expected_l == actual_l =>
        {
            if extends(actual_r, expected_r) {
                return Ok(());
            }
        }
        (Type::Product(expected_l, expected_r), Type::Product(actual_l, actual_r))
            if expected_r == actual_r =>
        {
            if extends(actual_l, expected_l) {
                return Ok(());
            }
        }
        (Type::Func(expected_l, expected_r), Type::Func(actual_l, actual_r))
            if expected_l == actual_l =>
        {
            if extends(actual_r, expected_r) {
                return Ok(());
            }
        }
        (Type::Func(expected_l, expected_r), Type::Func(actual_l, actual_r))
            if expected_r == actual_r =>
        {
            // it is reversed because argument type of function is contravariant
            if extends(expected_l, actual_l) {
                return Ok(());
            }
        }
        _ => {}
    }
    if expected != actual {
        return Err(VerificationError::MismatchedTargetType {
            expected: expected.clone(),
            actual: actual.clone(),
        });
    }
    Ok(())
}

/// Checks whether `sub` type extends `sup` type.
///
/// It is equivalent to whether a value of `sub` type is assignable to a variable of `sup` type.
fn extends(sub: &Type, sup: &Type) -> bool {
    sub == sup || sup == &Type::Placeholder
}

fn find_expr_type<'a>(
    env: &ProofContext<'a>,
    expr: &Expression<'a>,
) -> Result<Type<'a>, VerificationError<'a>> {
    match expr {
        Expression::Var(var_id) => env
            .get_var_type(var_id)
            .cloned()
            .ok_or_else(|| VerificationError::VariableNotFound(var_id.clone())),
        Expression::Pair(lhs, rhs) => Ok(Type::Product(
            find_expr_type(env, &lhs)?.clone().into(),
            find_expr_type(env, &rhs)?.clone().into(),
        )),
        Expression::Left(expr) => {
            let Type::Product(left_ty, _) = find_expr_type(env, expr)? else {
                return Err(VerificationError::ExpectedType("Product"));
            };
            Ok(*left_ty)
        }
        Expression::Right(expr) => {
            let Type::Product(_, right_ty) = find_expr_type(env, expr)? else {
                return Err(VerificationError::ExpectedType("Product"));
            };
            Ok(*right_ty)
        }
        Expression::InL(expr) => {
            let ty = find_expr_type(env, expr)?;
            Ok(Type::Sum(ty.into(), Type::Placeholder.into()))
        }
        Expression::InR(expr) => {
            let ty = find_expr_type(env, expr)?;
            Ok(Type::Sum(Type::Placeholder.into(), ty.into()))
        }
        Expression::Case { case_left, .. } => {
            let Expression::Lambda { body, .. } = case_left.as_ref() else {
                return Err(VerificationError::ExpectedExpression("lambda"));
            };
            find_expr_type(env, body)
        }
        Expression::Lambda {
            param_type, body, ..
        } => Ok(Type::Func(
            param_type.clone().into(),
            find_expr_type(env, body)?.into(),
        )),
        Expression::Apply { func, .. } => {
            let func_ty = find_expr_type(env, func)?;
            let Type::Func(_, ret_type) = func_ty else {
                return Err(VerificationError::ExpectedExpression("lambda"));
            };
            Ok(*ret_type)
        }
    }
}

#[derive(Debug, Clone, Default)]
struct ProofContext<'a> {
    assumptions: HashMap<AssumptionId<'a>, &'a Assumption<'a>>,
    var_type_dict: HashMap<VarId<'a>, Vec<&'a Type<'a>>>,
}

impl<'a> ProofContext<'a> {
    fn from_env(env: &'a Env<'a>) -> Result<Self, VerificationError<'a>> {
        let mut this = Self::default();
        for assumption in env.assumptions() {
            if this
                .assumptions
                .insert(assumption.id(), assumption)
                .is_some()
            {
                return Err(VerificationError::DuplicatedAssumptionId(assumption.id()));
            }
            this.var_type_dict
                .entry(assumption.var_id())
                .or_default()
                .push(assumption.ty());
        }
        Ok(this)
    }

    fn get_var_type(&self, var_id: &VarId<'a>) -> Option<&'a Type<'a>> {
        self.var_type_dict.get(var_id)?.last().map(|v| &**v)
    }

    fn get(&self, id: &AssumptionId<'a>) -> Option<&'a Assumption<'a>> {
        self.assumptions.get(id).cloned()
    }

    fn push(&mut self, assumption: &'a Assumption<'a>) {
        self.assumptions.insert(assumption.id(), assumption);
        self.var_type_dict
            .entry(assumption.var_id())
            .or_default()
            .push(assumption.ty());
    }

    fn pop(&mut self, id: &AssumptionId<'a>) -> Option<&'a Assumption<'a>> {
        let ret = self.assumptions.remove(id);
        if let Some(assumption) = ret {
            if let Some(stack) = self.var_type_dict.get_mut(&assumption.var_id()) {
                debug_assert!(!stack.is_empty());
                stack.pop();
            }
        }
        ret
    }
}
