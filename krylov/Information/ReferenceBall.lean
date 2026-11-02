import krylov.Information.CompactAdmissibleUpper

/-!
Article: main_krylov, thm:C, genuine compact admissible reference ball.
Use: derive positivity and full reference activity for every physically
admissible nearby base, before every perturbation budget and method.
Source: the standard real self-adjoint matrix submodule, fixed root
congruence, actual CG analyticity and compact finite-dimensional balls.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.LinearAlgebra krylov.Stability krylov.Correction krylov.Methods
open scoped BigOperators MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual physical base with a symmetric relative displacement in the original reference metric.
Use: its genuine closed parameter balls contain every original admissible source base.
Article: main_krylov, thm:C, A₀(Z)=A¹ᐟ²(I+Z)A¹ᐟ². -/
def referenceBaseChart (A : Matrix (Fin n) (Fin n) ℝ)
    (Z : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  inverseFormMap (metricRoot A)⁻¹ (1+Z.val)

/-- The actual symmetric base chart starts at the original positive physical reference.
Use: local genuine CG regularity is based at exactly the source reference.
Article: main_krylov, thm:C, A₀(0)=A.
Proof: the true zero displacement vanishes under the fixed root congruence. -/
theorem referenceBaseChart_zero (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    referenceBaseChart A 0=A := by
  simp only [referenceBaseChart,ZeroMemClass.coe_zero,add_zero,inverseRootForm_one A hA]

/-- The actual physical symmetric base chart is analytic at every genuine relative displacement.
Use: varying admissible bases satisfy the true joint compact reference regularity hypotheses.
Article: main_krylov, thm:C, analytic full base chart.
Proof: the true submodule inclusion and the fixed physical congruence are continuous linear maps. -/
theorem referenceBaseChart_analyticAt (A : Matrix (Fin n) (Fin n) ℝ)
    (Z : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    AnalyticAt ℝ (referenceBaseChart A) Z := by
  exact ((inverseFormMap (metricRoot A)⁻¹).toContinuousLinearMap.analyticAt _).comp
    (analyticAt_const.add ((selfAdjoint.submodule ℝ _).subtypeL.analyticAt Z))

/-- The genuine physical symmetric base chart is positive throughout the strict unit relative ball.
Use: all actual normalization and CG inverse domains lie in genuine positive metrics.
Article: main_krylov, thm:C, positivity of the full admissible base tube.
Proof: true self-adjointness gives real matrix symmetry; the strict spectral
unit ball has I+Z positive. The invertible original root congruence preserves positivity.
-/
theorem referenceBaseChart_posDef (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (Z : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) (hZ : ‖Z‖<1) :
    (referenceBaseChart A Z).PosDef := by
  have hsym : Z.val.IsSymm := (show Z.val.IsHermitian from Z.property).isSymm
  have hp : (1+Z.val).PosDef := by
    simpa only [one_smul] using (strict_shifted_posDef _ hsym hZ).2
  exact inverseForm_posDef _ _ (Matrix.isUnit_nonsing_inv_det _ (metricRoot_det_unit A hA)) hp

/-- Every point of the strict genuine reference ball has a positive physical base on an actual neighborhood.
Use: the compact varying-reference tube requires true nearby positive metrics at each reference, not only positivity on the compact.
Article: main_krylov, thm:C, positive open reference-chart domain.
Proof: the strict spectral-norm ball is open and every one of its charted bases is positive. -/
theorem referenceBaseChart_eventually_posDef (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (Z : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) (hZ : ‖Z‖<1) :
    ∀ᶠ Y in 𝓝 Z, (referenceBaseChart A Y).PosDef := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hZ] with Y hY
  exact referenceBaseChart_posDef A hA Y hY

/-- A genuine closed relative reference ball preserves positive metrics and the full active spectral count of the source reference.
Use: this derived compact contains every original nearby admissible base uniformly before all budget profiles.
Article: main_krylov, thm:C, existence of r₀ and the full nondegenerate compact reference set.
Proof: the actual chart is positive and analytic around zero. Genuine CG
regularity makes its strictly positive last preterminal error continuous.
On a sufficiently small closed ball that true error stays positive. The
exact CG stopping criterion and finite spectral-cardinality bound then
force full active support at every base in the compact.
-/
theorem referenceBaseChart_full_ball {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1)))
    (hcount : referenceAtomCount A hA g=N+1) :
    ∃ r₀ : ℝ, 0<r₀ ∧ r₀<1 ∧
      ∀ Z : selfAdjoint.submodule ℝ (Matrix (Fin (N+1)) (Fin (N+1)) ℝ), ‖Z‖≤r₀ →
        ∃ hB : (referenceBaseChart A Z).PosDef,
          referenceAtomCount (referenceBaseChart A Z) hB g=N+1 := by
  -- The actual source last CG error is positive, and its full symmetric chart is regular.
  have hφ : 0<‖cgCanonicalError (referenceBaseChart A 0) g N‖ := by
    rw [referenceBaseChart_zero A hA]
    exact canonical_error_pos A hA _ (cg_nonstagnation A hA g N (by omega))
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator (referenceBaseChart A 0)) g i≠0 := by
    rw [referenceBaseChart_zero A hA]
    exact cg_nonstagnation A hA g i (by omega)
  have hpos := referenceBaseChart_eventually_posDef A hA 0 (by simp)
  have he := (referenceCanonicalError_analyticAt (referenceBaseChart A) (fun _ => g) 0 N
    (referenceBaseChart_analyticAt A 0) hpos analyticAt_const hpre).continuousAt.norm
  have hepos : ∀ᶠ Z in 𝓝 0, 0<‖cgCanonicalError (referenceBaseChart A Z) g N‖ :=
    he.preimage_mem_nhds (isOpen_Ioi.mem_nhds hφ)
  obtain ⟨ε,hε,hεbound⟩ := Metric.eventually_nhds_iff.mp hepos
  let r₀ := min (1/2 : ℝ) (ε/2)
  have hr₀ : 0<r₀ := lt_min (by norm_num) (half_pos hε)
  have hr₁ : r₀<1 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨r₀,hr₀,hr₁,?_⟩
  intro Z hZ
  -- Genuine last-error positivity excludes early stopping on the whole closed ball.
  have hB := referenceBaseChart_posDef A hA Z (hZ.trans_lt hr₁)
  have hn : 0<‖cgCanonicalError (referenceBaseChart A Z) g N‖ :=
    hεbound (by simpa only [dist_zero_right] using hZ.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hε)))
  have hgrad : CG.gradient (cgOperator (referenceBaseChart A Z)) g N≠0 := by
    intro hz
    have hez : cgCanonicalError (referenceBaseChart A Z) g N=0 := by
      simp only [cgCanonicalError,hz,map_zero]
    rw [hez,norm_zero] at hn
    exact (lt_irrefl (0 : ℝ)) hn
  have hactive : N<referenceAtomCount (referenceBaseChart A Z) hB g := by
    by_contra hc
    exact hgrad ((cg_stopping_iff _ hB g N).mpr (by omega))
  refine ⟨hB,?_⟩
  have hle := referenceAtomCount_le _ hB g
  omega

/-- Every original symmetric physical base is reconstructed exactly by its genuine relative displacement.
Use: the compact reference ball covers the whole original physical scenario class.
Article: main_krylov, thm:C, exact physical base coverage.
Proof: the true inverse-root relative displacement reconstructs B−A;
adding the original base under its fixed positive-root congruence gives B.
-/
theorem referenceBaseChart_reconstruct (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hB : B.IsSymm) :
    referenceBaseChart A ⟨relativeOperator A (B-A),
      (Matrix.isHermitian_iff_isSymm.mpr (relativeOperator_isSymm _ _ (hB.sub hA.1.isSymm)))⟩=B := by
  -- Use the genuine root reconstruction before cancelling the physical displacement.
  rw [referenceBaseChart,inverseRootForm A _ hA,Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,
    metricRoot_square A hA,relativeOperator_reconstruct A (B-A) hA]
  abel


end
end krylov.Information
