import krylov.Correction.PlanarAttainment
import krylov.Information.AdmissibleTwin

/-!
Article: main_krylov, thm:C, admissible all-profile planar lower scenarios.
Use: construct the actual two signed bases and every independent primitive
budget with the source slack, before invoking information-fibre estimates.
Source: the proved planar spectral witness, exact rank-one norms and genuine
Loewner base-change budget transfer.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Secant krylov.Reference krylov.LinearAlgebra krylov.Correction
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {n : ℕ}

/-- The actual signed planar source scenario with the original all-profile budget slack.
Use: both signs share their cross coefficients while their base and hidden diagonals differ.
Article: main_krylov, thm:C, A₀^± and E_l^± with t=1−W₀. -/
def planarLowerScenario (e f : EuclideanSpace ℝ (Fin n)) (ω : ℕ → ℝ) (w : ℝ)
    (N : ℕ) (a γ σ : ℝ) : Scenario n :=
  let W := ∑ i∈range N, ω i
  let t := 1-W
  { base := 1+planarMatrix f e (σ*t*γ*W) 0 0
    increment := fun i => planarMatrix e f (t*ω i*(σ*γ)) (t*ω i*a) (t*ω i*(-(σ*γ)))
    terminal := planarMatrix e f (σ*t*w) 0 0
    correction := 0 }

/-- The actual relative spectral budget at the identity is the genuine matrix spectral norm.
Use: the canonical lower construction is subsequently transported to the physical reference.
Article: main_krylov, thm:C, canonical budget normalization.
Proof: the genuine positive square root and inverse of the identity are the identity. -/
theorem relativeBudget_one (D : Matrix (Fin n) (Fin n) ℝ) : relativeBudget 1 D=‖D‖ := by
  simp only [relativeBudget,relativeOperator,metricRoot,CFC.sqrt_one,inv_one,Matrix.one_mul,
    Matrix.mul_one,chebyshev1.opNorm]

/-- A real single-direction planar diagonal has exactly its absolute scalar spectral norm.
Use: bound both the true hidden base displacement and the terminal perturbation.
Article: main_krylov, thm:C, ‖δeeᵀ‖=|δ|.
Proof: the exact true rank-one matrix norm is the product of its two unit generating norms. -/
theorem planar_diagonal_norm (e f : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (δ : ℝ) :
    ‖planarMatrix e f δ 0 0‖=|δ| := by
  have hr : ‖vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)‖=1 := by
    simpa only [chebyshev1.opNorm,WithLp.toLp_ofLp,he,mul_one] using
      spectral_norm_rankOne (WithLp.ofLp e) (WithLp.ofLp e)
  simp only [planarMatrix,zero_smul,add_zero,norm_smul,Real.norm_eq_abs,hr,mul_one]

/-- Both actual signed planar scenarios satisfy all original canonical source budgets for every nonnegative profile.
Use: admissibility is derived for the explicit operators rather than assumed in the lower-bound theorem.
Article: main_krylov, thm:C, t-budget slack and admissible unknown-base scenarios.
Proof: the hidden base displacement has norm at most W and thus dominates
(1−W)I while remaining positive. Every actual planar increment has norm at
most (1−W)ω_l; the terminal rank-one matrix has norm (1−W)w. The proved
Loewner base-change estimate transfers each budget to that same actual base.
Intermediate perturbations vanish, including every zero-budget case.
-/
theorem planarLowerScenario_admissible (e f : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hf : ‖f‖=1) (hef : inner ℝ e f=0)
    (ω : ℕ → ℝ) (w τ r : ℝ) (N : ℕ)
    (hω : ∀ i∈range N, 0≤ω i) (hw : 0≤w) (hτ : 0≤τ)
    (hW : (∑ i∈range N, ω i)<1) (hWr : (∑ i∈range N, ω i)≤r)
    (a γ σ : ℝ) (hγ : 0≤γ) (hac : a^2+γ^2=1) (hσ : σ^2=1) :
    (planarLowerScenario e f ω w N a γ σ).Admissible N 1 r ω w τ := by
  -- The same actual positive base and scalar slack serve every independent budget.
  let W := ∑ i∈range N, ω i
  let t := 1-W
  let S := planarLowerScenario e f ω w N a γ σ
  have hW₀ : 0≤W := sum_nonneg hω
  have ht : 0<t := by dsimp only [t]; linarith
  have ht₁ : t≤1 := by dsimp only [t]; linarith
  have hγ₁ : γ≤1 := by nlinarith [sq_nonneg a]
  have hσabs : |σ|=1 := by nlinarith [sq_abs σ,abs_nonneg σ]
  have hδ : |σ*t*γ*W|≤W := by
    rw [abs_mul,abs_mul,abs_mul,hσabs,abs_of_nonneg ht.le,abs_of_nonneg hγ,
      abs_of_nonneg hW₀,one_mul]
    calc
      t*γ*W ≤ t*W := mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hγ₁ ht.le).trans_eq (mul_one t)) hW₀
      _ ≤ 1*W := mul_le_mul_of_nonneg_right ht₁ hW₀
      _ = W := one_mul W
  have hbase : relativeBudget 1 (S.base-1)≤W := by
    rw [relativeBudget_one]
    change ‖(1+planarMatrix f e (σ*t*γ*W) 0 0)-1‖≤W
    rw [add_sub_cancel_left,planar_diagonal_norm f e hf]
    exact hδ
  have hsym : S.base.IsSymm := by
    change (1+planarMatrix f e (σ*t*γ*W) 0 0).IsSymm
    exact Matrix.isSymm_one.add (planarMatrix_isSymm _ _ _ _ _)
  have hp := relative_displacement_base 1 S.base Matrix.PosDef.one hsym hW₀ hW hbase
  have hunit : ‖planarMatrix e f (σ*γ) a (-(σ*γ))‖≤1 := by
    simpa only [neg_neg,chebyshev1.opNorm] using
      planar_spectral_norm_le e f he hf hef (-(σ*γ)) a (by nlinarith [hσ])
  refine ⟨hp.2.2,hbase.trans hWr,?_,planarMatrix_isSymm _ _ _ _ _,?_,?_⟩
  · intro i hi
    refine ⟨planarMatrix_isSymm _ _ _ _ _,?_⟩
    apply relative_budget_change 1 S.base (S.increment i) Matrix.PosDef.one hp.2.2
      (planarMatrix_isSymm _ _ _ _ _) ht.le (hω i (mem_range.mpr hi)) hp.1
    rw [relativeBudget_one]
    change ‖planarMatrix e f (t*ω i*(σ*γ)) (t*ω i*a) (t*ω i*(-(σ*γ)))‖≤t*ω i
    rw [planarMatrix_scale,norm_smul,Real.norm_of_nonneg (mul_nonneg ht.le (hω i (mem_range.mpr hi)))]
    exact (mul_le_mul_of_nonneg_left hunit (mul_nonneg ht.le (hω i (mem_range.mpr hi)))).trans_eq (mul_one _)
  · apply relative_budget_change 1 S.base S.terminal Matrix.PosDef.one hp.2.2
      (planarMatrix_isSymm _ _ _ _ _) ht.le hw hp.1
    rw [relativeBudget_one]
    change ‖planarMatrix e f (σ*t*w) 0 0‖≤t*w
    rw [planar_diagonal_norm e f he,abs_mul,abs_mul,hσabs,abs_of_nonneg ht.le,abs_of_nonneg hw,one_mul]
  · intro i _
    refine ⟨Matrix.isSymm_zero,?_⟩
    simpa only [S,planarLowerScenario,Pi.zero_apply,relativeBudget,relativeOperator,
      Matrix.mul_zero,Matrix.zero_mul,chebyshev1.opNorm,norm_zero] using hτ

/-- Nonsingular physical transport preserves every primitive source admissibility constraint.
Use: the explicit canonical lower family gives actual physical scenarios in the same reference ball and individual budgets.
Article: main_krylov, thm:C, transport of admissible indistinguishable lower scenarios.
Proof: genuine congruence preserves positivity and every true relative
spectral budget. Linearity transports the base-radius difference; all
increments, terminal and intermediate defects use the same actual base.
-/
theorem Scenario.inPhysical_admissible (S : Scenario n) (N : ℕ)
    (A D : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hD : IsUnit D.det)
    (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) (hS : S.Admissible N A r ω w τ) :
    (S.inPhysical D).Admissible N (inverseFormMap D A) r ω w τ := by
  -- Transport all constraints through one actual invertible physical congruence.
  refine ⟨inverseForm_posDef D S.base hD hS.1,?_,?_,?_,?_,?_⟩
  · have hsym : (S.base-A).IsSymm := by
      simp only [Matrix.IsSymm,transpose_sub,hS.1.1.isSymm.eq,hA.1.isSymm.eq]
    have he : (S.inPhysical D).base-inverseFormMap D A=inverseFormMap D (S.base-A) :=
      (map_sub (inverseFormMap D) S.base A).symm
    exact (congrArg (relativeBudget (inverseFormMap D A)) he).le.trans
      ((inverseForm_budget D A (S.base-A) hD hA hsym).le.trans hS.2.1)
  · intro i hi
    have he := hS.2.2.1 i hi
    exact ⟨inverseForm_isSymm D _ he.1,
      (inverseForm_budget D S.base (S.increment i) hD hS.1 he.1).le.trans he.2⟩
  · exact inverseForm_isSymm D S.terminal hS.2.2.2.1
  · exact (inverseForm_budget D S.base S.terminal hD hS.1 hS.2.2.2.1).le.trans hS.2.2.2.2.1
  · intro i hi
    have he := hS.2.2.2.2.2 i hi
    exact ⟨inverseForm_isSymm D _ he.1,
      (inverseForm_budget D S.base (S.correction i) hD hS.1 he.1).le.trans he.2⟩

/-- The inverse canonical root transports the identity reference to the original physical positive reference exactly.
Use: the lower-family radius is measured against the original physical A, rather than an auxiliary canonical base.
Article: main_krylov, thm:C, exact original-reference transport.
Proof: the actual positive root is symmetric and invertible; its inverse
coordinate map cancels twice and its genuine square is A. -/
theorem inverseRootForm_one (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    inverseFormMap (metricRoot A)⁻¹ 1=A := by
  change ((metricRoot A)⁻¹)ᵀ⁻¹*1*((metricRoot A)⁻¹)⁻¹=A
  rw [Matrix.mul_one,transpose_nonsing_inv,Matrix.nonsing_inv_nonsing_inv _ (metricRoot_det_unit A hA)]
  rw [Matrix.nonsing_inv_nonsing_inv _ (by simpa only [det_transpose] using metricRoot_det_unit A hA)]
  rw [(metricRoot_isSymm A).eq,metricRoot_square A hA]

/-- Both actual signed planar lower scenarios satisfy all original physical source budgets.
Use: the unknown-base construction stays in the prescribed physical reference ball for every profile, including zero entries.
Article: main_krylov, thm:C, admissible all-profile physical lower scenarios.
Proof: the explicit canonical family already satisfies every primitive
constraint with its true base slack. Genuine inverse-root transport preserves
all those budgets and maps the identity reference exactly to the original A.
-/
theorem physical_planarLowerScenario_admissible (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e f : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hf : ‖f‖=1) (hef : inner ℝ e f=0)
    (ω : ℕ → ℝ) (w τ r : ℝ) (N : ℕ)
    (hω : ∀ i∈range N, 0≤ω i) (hw : 0≤w) (hτ : 0≤τ)
    (hW : (∑ i∈range N, ω i)<1) (hWr : (∑ i∈range N, ω i)≤r)
    (a γ σ : ℝ) (hγ : 0≤γ) (hac : a^2+γ^2=1) (hσ : σ^2=1) :
    ((planarLowerScenario e f ω w N a γ σ).inPhysical (metricRoot A)⁻¹).Admissible N A r ω w τ := by
  have hS := planarLowerScenario_admissible e f he hf hef ω w τ r N hω hw hτ hW hWr a γ σ hγ hac hσ
  have ht := Scenario.inPhysical_admissible _ N 1 (metricRoot A)⁻¹ Matrix.PosDef.one
    (Matrix.isUnit_nonsing_inv_det _ (metricRoot_det_unit A hA)) r ω w τ hS
  simpa only [inverseRootForm_one A hA] using ht

end
end krylov.Information
