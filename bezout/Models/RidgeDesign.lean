import bezout.Models.Ridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: bezout, the rank-one Hessian and square-root design in Equation `eq:experiment-ridge`.
Use: constructs the design matrix and labels explicitly from the two spectral
values; verifies the square-root and inverse identities required by the literal ridge objective.
Proof: the unit-vector projection is idempotent and self-adjoint; its two
spectral coefficients multiply separately.
-/

namespace bezout.Models.Ridge
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orthogonal rank-one projection along the distinguished unit direction. -/
def projection (v : E) : E →L[ℝ] E := (innerSL ℝ v).smulRight v

/-- A two-eigenvalue operator, written in the article's rank-one form. -/
def spectralMap (v : E) (a b : ℝ) : E →L[ℝ] E :=
  a • ContinuousLinearMap.id ℝ E+(b-a) • projection v

/-- Literal rank-one action of the two-eigenvalue operator. -/
theorem spectralMap_apply (v : E) (a b : ℝ) (x : E) :
    spectralMap v a b x=a • x+((b-a)*inner ℝ v x) • v := by
  simp only [spectralMap, projection, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]

/-- Unit-direction spectral maps are closed under composition with componentwise products. -/
theorem spectralMap_comp (v : E) (hv : ‖v‖=1) (a b c d : ℝ) (x : E) :
    spectralMap v a b (spectralMap v c d x)=spectralMap v (a*c) (b*d) x := by
  simp only [spectralMap_apply, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_one]
  module

/-- The unit spectral map is exactly the identity on the full space. -/
theorem spectralMap_one (v x : E) : spectralMap v 1 1 x=x := by
  simp [spectralMap_apply]

/-- The literal rank-one operator is self-adjoint. -/
theorem spectralMap_symmetric (v : E) (a b : ℝ) :
    (spectralMap v a b).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (spectralMap v a b x) y=inner ℝ x (spectralMap v a b y)
  simp only [spectralMap_apply, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, conj_trivial]
  rw [real_inner_comm v x]
  ring

/-- The physical positive rank-one Hessian has nonnegative quadratic energy. -/
theorem spectralMap_nonneg (v : E) (a b : ℝ) (ha : 0≤a) (hab : a≤b) (x : E) :
    0 ≤ inner ℝ (spectralMap v a b x) x := by
  simp only [spectralMap_apply, inner_add_left, inner_smul_left, conj_trivial,
    real_inner_self_eq_norm_sq]
  have hsq := sq_nonneg (inner ℝ v x)
  nlinarith [mul_nonneg ha (sq_nonneg ‖x‖), mul_nonneg (sub_nonneg.mpr hab) hsq]

/-- Explicit positive square root in the two spectral subspaces. -/
def root (v : E) (μ L ρ : ℝ) : E →L[ℝ] E :=
  spectralMap v (Real.sqrt (μ-ρ)) (Real.sqrt (L-ρ))

/-- Explicit inverse square root of the regularized Hessian. -/
def inverseRoot (v : E) (μ L ρ : ℝ) : E →L[ℝ] E :=
  spectralMap v (1/Real.sqrt (μ-ρ)) (1/Real.sqrt (L-ρ))

/-- The constructed root squares to the required regularized Hessian. -/
theorem root_square (v : E) (hv : ‖v‖=1) (μ L ρ : ℝ) (hμ : ρ≤μ) (hL : ρ≤L) (x : E) :
    root v μ L ρ (root v μ L ρ x)=spectralMap v μ L x-ρ • x := by
  unfold root
  rw [spectralMap_comp v hv]
  simp only [← sq, Real.sq_sqrt (sub_nonneg.mpr hμ), Real.sq_sqrt (sub_nonneg.mpr hL),
    spectralMap_apply]
  module

/-- The constructed inverse root is the actual inverse of the square root. -/
theorem root_inverse (v : E) (hv : ‖v‖=1) (μ L ρ : ℝ) (hμ : ρ<μ) (hL : ρ<L) (x : E) :
    root v μ L ρ (inverseRoot v μ L ρ x)=x := by
  unfold root inverseRoot
  rw [spectralMap_comp v hv]
  rw [mul_one_div_cancel (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hμ))),
    mul_one_div_cancel (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hL))), spectralMap_one]

/-- Actual scaled square-root design in the worker objective. -/
def design (d : ℝ) (v : E) (μ L ρ : ℝ) : E →L[ℝ] E := Real.sqrt d • root v μ L ρ

/-- Actual worker label obtained by applying the inverse square root to c. -/
def label (d : ℝ) (v : E) (μ L ρ : ℝ) (c : E) : E :=
  Real.sqrt d • inverseRoot v μ L ρ c

/-- The explicit square-root design is self-adjoint in the physical Hilbert space. -/
theorem design_symmetric (d : ℝ) (v : E) (μ L ρ : ℝ) :
    (design d v μ L ρ).toLinearMap.IsSymmetric := by
  intro y z
  change inner ℝ (Real.sqrt d • root v μ L ρ y) z=inner ℝ y (Real.sqrt d • root v μ L ρ z)
  simp only [inner_smul_left, inner_smul_right, conj_trivial]
  exact congrArg (fun t : ℝ => Real.sqrt d*t) (spectralMap_symmetric v _ _ y z)

/-- The explicit spectral root is positive for the article's ordered spectral bounds. -/
theorem root_nonneg (v : E) (μ L ρ : ℝ) (hμL : μ≤L) (x : E) :
    0 ≤ inner ℝ (root v μ L ρ x) x :=
  spectralMap_nonneg v _ _ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith)) x

/-- Both algebraic design identities hold for the actual constructed matrices and labels. -/
theorem design_identities (d : ℝ) (hd : 0≤d) (v : E) (hv : ‖v‖=1)
    (μ L ρ : ℝ) (hμ : ρ<μ) (hL : ρ<L) (c : E) :
    (∀ x, design d v μ L ρ (design d v μ L ρ x)=d • (spectralMap v μ L x-ρ • x)) ∧
    design d v μ L ρ (label d v μ L ρ c)=d • c := by
  constructor
  · intro x
    simp only [design, smul_apply, map_smul, smul_smul]
    rw [← sq, Real.sq_sqrt hd, root_square v hv μ L ρ hμ.le hL.le]
  · simp only [design, label, smul_apply, map_smul, smul_smul]
    rw [← sq, Real.sq_sqrt hd, root_inverse v hv μ L ρ hμ hL]

/-- The article's literal square-root ridge construction has exactly gradient Hx-c. -/
theorem design_gradient [CompleteSpace E] (d : ℝ) (hd : 0<d) (v : E) (hv : ‖v‖=1)
    (μ L ρ : ℝ) (hμ : ρ<μ) (hL : ρ<L) (c x : E) :
    HasGradientAt (objective d ρ (design d v μ L ρ) (label d v μ L ρ c))
      (spectralMap v μ L x-c) x := by
  have hi := design_identities d hd.le v hv μ L ρ hμ hL c
  apply hasGradientAt_objective d ρ (ne_of_gt hd) _ _ _ _ _ x hi.1 hi.2
  exact design_symmetric d v μ L ρ

end
end bezout.Models.Ridge
