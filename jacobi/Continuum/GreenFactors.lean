import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
A strictly positive symmetric kernel with the one-dimensional interval
factorization has canonical positive left and right factors, normalized at
zero. Each factor is locally a constant multiple of a Green column with
its source outside that neighborhood. The actual operator application
proves all kernel hypotheses by coercivity before using this construction.
Source: the elementary one-dimensional Green product representation.
Use: local column identities construct its classical equation without an additional global ODE existence assumption.
-/
namespace jacobi.Continuum
noncomputable section
open Set Real

/-- The right factor selected by Green columns, normalized to one at zero.
Use: local column identities construct its classical equation without an additional global ODE existence assumption.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def greenRightFactor (G : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  if x≤0 then G x x/G x 0 else G 0 x/G 0 0

/-- The left factor selected by Green columns, normalized by the zero Green diagonal.
Use: its product with the right factor reconstructs the actual Green kernel with unit Wronskian.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def greenLeftFactor (G : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  if x≤0 then G x 0 else G 0 0*G x x/G 0 x

/-- Both canonical Green factors are strictly positive everywhere.
Use: all later ratios and logarithmic derivatives have their positivity proved from the actual inverse kernel.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: each branch is a product or quotient of strictly positive kernel values. -/
theorem greenFactors_pos {G : ℝ → ℝ → ℝ} (hG : ∀ x y,0<G x y) (x : ℝ) :
    0<greenRightFactor G x ∧ 0<greenLeftFactor G x := by
  have hxx := hG x x
  have hx0 := hG x 0
  have h0x := hG 0 x
  have h00 := hG 0 0
  unfold greenRightFactor greenLeftFactor
  split_ifs <;> constructor <;> positivity

/-- Each right factor is locally one fixed right-hand Green column ratio.
Use: gives classical derivatives at every point by moving the column source strictly to its left.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: apply interval factorization at y when y<=0 and at zero when y>0,
then cancel the strictly positive kernel denominators. -/
theorem greenRightFactor_column {G : ℝ → ℝ → ℝ} (hG : ∀ x y,0<G x y)
    (hM : ∀ {x a z : ℝ},x≤a → a≤z → G x z=(G x a/G a a)*G a z)
    {a y : ℝ} (ha : a≤0) (hay : a≤y) : greenRightFactor G y=G a y/G a 0 := by
  -- The normalization changes at zero but both branches obey the same column ratio.
  unfold greenRightFactor
  by_cases hy : y≤0
  · rw [ite_eq_left hy]
    have h := hM hay hy
    field_simp [(hG y 0).ne',(hG a 0).ne',(hG y y).ne'] at h ⊢
    nlinarith
  · rw [ite_eq_right hy]
    have h := hM ha (le_of_not_ge hy)
    field_simp [(hG a 0).ne',(hG 0 0).ne'] at h ⊢
    nlinarith

/-- Each left factor is locally a constant multiple of one fixed left-hand Green column.
Use: gives classical derivatives at every point by moving the source strictly to its right.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: apply interval factorization at zero or y, according to y's sign,
and cancel the positive kernel denominators. -/
theorem greenLeftFactor_column {G : ℝ → ℝ → ℝ} (hG : ∀ x y,0<G x y)
    (hM : ∀ {x a z : ℝ},x≤a → a≤z → G x z=(G x a/G a a)*G a z)
    {b y : ℝ} (hb : 0≤b) (hyb : y≤b) :
    greenLeftFactor G y=G y b*G 0 0/G 0 b := by
  -- Both signs share one homogeneous column representation in a whole neighborhood of y.
  unfold greenLeftFactor
  by_cases hy : y≤0
  · rw [ite_eq_left hy]
    have h := hM hy hb
    field_simp [(hG 0 b).ne',(hG 0 0).ne'] at h ⊢
    nlinarith
  · rw [ite_eq_right hy]
    have h := hM (le_of_not_ge hy) hyb
    field_simp [(hG 0 y).ne',(hG 0 b).ne',(hG y y).ne'] at h ⊢
    nlinarith [congrArg (fun z : ℝ => z*G 0 0) h]

/-- The canonical positive factors reconstruct the entire ordered Green kernel.
Use: their classical equations and Wronskian yield the actual Green diagonal identity.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: split the ordered pair at zero. Interval factorization at zero or at
one endpoint gives each case after positive denominator cancellation. -/
theorem greenFactors_product {G : ℝ → ℝ → ℝ} (hG : ∀ x y,0<G x y)
    (hM : ∀ {x a z : ℝ},x≤a → a≤z → G x z=(G x a/G a a)*G a z)
    {x y : ℝ} (hxy : x≤y) : G x y=greenLeftFactor G x*greenRightFactor G y := by
  -- The three possible locations of zero give all ordered kernel pairs.
  unfold greenLeftFactor greenRightFactor
  by_cases hy : y≤0
  · rw [ite_eq_left hy,ite_eq_left (hxy.trans hy)]
    have h := hM hxy hy
    field_simp [(hG y 0).ne',(hG y y).ne'] at h ⊢
    nlinarith
  · rw [ite_eq_right hy]
    by_cases hx : x≤0
    · rw [ite_eq_left hx]
      have h := hM hx (le_of_not_ge hy)
      field_simp [(hG 0 0).ne'] at h ⊢
      nlinarith
    · rw [ite_eq_right hx]
      have h := hM (le_of_not_ge hx) hxy
      field_simp [(hG 0 x).ne',(hG 0 0).ne',(hG x x).ne'] at h ⊢
      nlinarith

end
end jacobi.Continuum
