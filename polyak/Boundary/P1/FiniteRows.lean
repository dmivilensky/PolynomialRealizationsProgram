import polyak.Boundary.P1.FiniteIdentity
import polyak.Numerics.TensorRows

/-! Checked row reduction and final source identity for the finite P1 prefix. -/
noncomputable section
namespace polyak.Boundary.P1
open Numerics.BivariateIdentity Numerics.TensorBernstein

def slackRowsIdentityCheck (n : ℕ) (σ : ℚ) (c : Certificate)
    (rows : Fin (c.degree0+1) → Expr) : Bool :=
  (slackExpression n σ).check (.mul (factorExpression n σ) (c.rowsExpression rows))

theorem scaledSlack_pos_of_rows {n : ℕ} {σ : ℚ} (c : Certificate)
    (rows : Fin (c.degree0+1) → Expr)
    (hr : ∀ i, (c.rowExpression i).check (rows i)=true)
    (he : slackRowsIdentityCheck n σ c rows=true) (hc : c.check=true)
    {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4) (ha : -z/2≤a ∧ a≤0) :
    0<scaledSlack n σ z a := by
  let x : ℝ := 4*z/3
  let y : ℝ := -2*a/z
  have hx : x∈Set.Icc 0 1 := by dsimp [x]; constructor <;> linarith
  have hy : y∈Set.Icc 0 1 := by
    dsimp [y]
    constructor
    · exact div_nonneg (by linarith) hz.le
    · rw [div_le_one hz]
      linarith [ha.1]
  have hxz : (3/4 : ℝ)*x=z := by dsimp [x]; ring
  have hya : -y*z/2=a := by dsimp [y]; field_simp
  have hp := c.value_pos hc hx hy
  have hs := Expr.check_sound he x y
  rw [slackExpression_value,Expr.value,factorExpression_value,c.rowsExpression_value rows hr,hxz,hya] at hs
  rw [hs]
  split_ifs <;> positivity

end polyak.Boundary.P1
