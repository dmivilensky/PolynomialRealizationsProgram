import polyak.Numerics.TensorIdentity

/-! Rowwise exact tensor identities avoid recomputing full bivariate expansions. -/
noncomputable section
namespace polyak.Numerics.TensorBernstein
open BivariateIdentity

def Certificate.rowExpression (c : Certificate) (i : Fin (c.degree0+1)) : Expr :=
  Expr.sum (List.ofFn fun j : Fin (c.degree1+1) =>
    .mul (.mul (.literal (c.coefficient i j)) (.pow .y j))
      (.pow (.add (.literal 1) (.mul (.literal (-1)) .y)) (c.degree1-j)))

def Certificate.rowsExpression (c : Certificate) (rows : Fin (c.degree0+1) → Expr) : Expr :=
  Expr.sum (List.ofFn fun i : Fin (c.degree0+1) =>
    .mul (.mul (rows i) (.pow .x i))
      (.pow (.add (.literal 1) (.mul (.literal (-1)) .x)) (c.degree0-i)))

theorem Certificate.rowExpression_value (c : Certificate) (i : Fin (c.degree0+1)) (x y : ℝ) :
    (c.rowExpression i).value x y=∑ j, (c.coefficient i j : ℝ)*basis c.degree1 j y := by
  simp only [Certificate.rowExpression,Expr.sum_value,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,Expr.value,basis,Rat.cast_one,Rat.cast_neg,neg_mul,one_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem Certificate.rowsExpression_value (c : Certificate) (rows : Fin (c.degree0+1) → Expr)
    (hr : ∀ i, (c.rowExpression i).check (rows i)=true) (x y : ℝ) :
    (c.rowsExpression rows).value x y=c.value x y := by
  simp only [Certificate.rowsExpression,Expr.sum_value,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,Expr.value,Rat.cast_one,Rat.cast_neg,neg_mul,one_mul]
  unfold Certificate.value
  apply Finset.sum_congr rfl
  intro i _
  rw [← Expr.check_sound (hr i),c.rowExpression_value]
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  unfold basis
  ring

end polyak.Numerics.TensorBernstein
