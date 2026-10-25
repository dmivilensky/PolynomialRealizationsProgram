import polyak.Boundary.P1.FiniteSource
import polyak.Numerics.TensorBernstein

/-!
Article: (p1slackpoly), tensor Bernstein on z∈[0,3/4], a=−θz/2.
Use: finite annotations are checked against the fixed Chebyshev recurrence source.
-/
noncomputable section
namespace polyak.Boundary.P1
open MvPolynomial Numerics.TensorBernstein

/-- Exact polynomial source in the two unit interval coordinates. -/
def slackSource (n : ℕ) (σ : ℚ) : Poly :=
  polynomialSlack n (C σ) (C (3/4)*X 0) (-X 1*(C (3/4)*X 0)*C (1/2))

/-- The upper slack has a harmless z² zero at the critical endpoint. -/
def slackFactor (n : ℕ) (σ : ℚ) : Poly :=
  if σ=1 ∧ 4≤n then (C (3/4)*X 0)^2 else 1

theorem slackSource_eval (n : ℕ) (σ : ℚ) (x y : ℝ) :
    eval₂Hom (Rat.castHom ℝ) ![x,y] (slackSource n σ)=
      scaledSlack n σ ((3/4)*x) (-y*((3/4)*x)/2) := by
  unfold slackSource
  rw [map_polynomialSlack]
  simp only [map_mul,map_neg,eval₂Hom_C,eval₂Hom_X',Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_one,Rat.coe_castHom]
  norm_num
  rw [polynomialSlack_eq]
  congr 1
  ring

theorem slackFactor_eval (n : ℕ) (σ : ℚ) (x y : ℝ) :
    eval₂Hom (Rat.castHom ℝ) ![x,y] (slackFactor n σ)=
      if σ=1 ∧ 4≤n then ((3/4)*x)^2 else 1 := by
  unfold slackFactor
  split_ifs <;> norm_num

theorem scaledSlack_pos_of_certificate {n : ℕ} {σ : ℚ} (c : Certificate)
    (he : slackSource n σ=slackFactor n σ*c.polynomial) (hc : c.check=true)
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
  have hya : -y*((3/4 : ℝ)*x)/2=a := by
    rw [hxz]
    dsimp [y]
    field_simp
  rw [hxz] at hya
  have hp := c.value_pos hc hx hy
  have hs := congrArg (eval₂Hom (Rat.castHom ℝ) ![x,y]) he
  rw [slackSource_eval,map_mul,c.eval_polynomial,slackFactor_eval,hxz,hya] at hs
  rw [hs]
  split_ifs <;> positivity

end polyak.Boundary.P1
