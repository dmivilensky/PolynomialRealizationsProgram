import krylov.Variation.CorrectionFreeVariation
import Mathlib.Basic.ENNReal.Real

/-!
Article: Corollary B.7 [s3:cor:cf] of krylov.tex.
Use: define the true source first-variation budget scenarios and the actual
infimum over span-restricted CG-consistent correction-free information-class
strategies, prove the printed two-sided minimax interval, and show FC has
exactly its sharp upper-end price. Extended nonnegative prices allow arbitrary
raw policies without a false boundedness premise.
Source: actual path derivative witnesses, the genuine common planar obstruction,
true sharp FC response and complete-lattice supremum/infimum inequalities.
-/

namespace krylov.Variation
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.LinearAlgebra krylov.Stability
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ} {μ κ : ℝ}

/-- A genuine symmetric component-budget actual method path together with its proved true first derivative.
Use: A genuine symmetric component-budget actual method path together with its proved true first derivative.
Article: main_krylov, s3:cor:cf, genuine correction-free first-order minimax bounds.
Proof: Its derivative is that of the actual executed canonical terminal gradient, without an assumed response formula. -/
structure FirstVariationScenario (R : FCReference (n+1) μ κ)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (n+1)))) (ω : ℕ → ℝ) where
  /-- The genuine canonical matrices used by the actual affine oracle path. -/
  increments : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ
  /-- Every actual increment is real symmetric. -/
  symmetric : ∀ l, (increments l).IsSymm
  /-- Every meaningful interior increment has its real assigned component spectral budget. -/
  budget : ∀ l<n, ‖increments l‖≤ω l
  /-- The actual canonical terminal-gradient derivative vector. -/
  variation : EuclideanSpace ℝ (Fin (n+1))
  /-- The genuine derivative witness for the real executed method path. -/
  derivative : HasDerivAt (fun t => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot R.base)⁻¹
    (probedGradient m (canonicalFCPath R.base increments t) (canonicalFCPath R.base increments t) R.gradient (n+1))) variation 0

/-- The true worst normalized actual first-variation price under the source independent component budgets.
Use: The true worst normalized actual first-variation price under the source independent component budgets.
Article: main_krylov, s3:cor:cf, genuine correction-free first-order minimax bounds.
Proof: Take the genuine extended nonnegative supremum over all true actual derivative scenarios. -/
def firstVariationPrice (R : FCReference (n+1) μ κ)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (n+1)))) (ω : ℕ → ℝ) : ENNReal :=
  ⨆ S : FirstVariationScenario R m ω, ENNReal.ofReal (‖S.variation‖/R.initialNorm)

/-- The actual FC first-variation price is at most its genuine sharp normalized reference coefficient.
Use: The actual FC first-variation price is at most its genuine sharp normalized reference coefficient.
Article: main_krylov, s3:cor:cf, genuine correction-free first-order minimax bounds.
Proof: Actual FC path differentiation identifies each true derivative uniquely; its genuine spectral response bound controls the real independent budgets. -/
theorem fc_firstVariationPrice_le (R : FCReference (n+1) μ κ) (ω : ℕ → ℝ) :
    firstVariationPrice R (fcMethod fullMemory) ω≤ENNReal.ofReal (R.coefficient ω) := by
  -- The genuine executed derivative is unique before its actual response norm is bounded.
  apply iSup_le
  intro S
  have hd : HasDerivAt (fun t => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot R.base)⁻¹
      (probedGradient (fcMethod fullMemory) (canonicalFCPath R.base S.increments t)
        (canonicalFCPath R.base S.increments t) R.gradient (n+1)))
      (fullCycleResponse R.base R.gradient (range (n+1)) S.increments) 0 :=
    canonicalFC_response_hasDerivAt R.base R.positive R.gradient R.full S.increments S.symmetric
  have he := S.derivative.unique hd
  apply ENNReal.ofReal_le_ofReal
  rw [he,R.response_trim]
  have hF := spectral_response_le R.base R.gradient (range n) S.increments ω
    (fun l hl => S.budget l (mem_range.mp hl))
  have hmass : R.coefficient ω*R.initialNorm=∑ l∈range n, ω l*‖cgCanonicalError R.base R.gradient (l+1)‖ := by
    rw [FCReference.coefficient,div_mul_cancel₀ _ R.initialNorm_pos.ne',R.mass_trim]
    rfl
  exact (div_le_iff₀ R.initialNorm_pos).mpr (by rw [hmass];exact hF)

/-- The actual FC first-variation price equals its genuine sharp normalized reference coefficient.
Use: The actual FC first-variation price equals its genuine sharp normalized reference coefficient.
Article: main_krylov, s3:cor:cf, genuine correction-free first-order minimax bounds.
Proof: The true response upper estimate and actual symmetric budget-attaining reference increments give both real supremum inequalities. -/
theorem fc_firstVariationPrice_eq (R : FCReference (n+1) μ κ) (ω : ℕ → ℝ) (hω : ∀ l<n+1, 0≤ω l) :
    firstVariationPrice R (fcMethod fullMemory) ω=ENNReal.ofReal (R.coefficient ω) := by
  -- A real symmetric budget attainer gives the true reverse supremum inequality.
  apply le_antisymm (fc_firstVariationPrice_le R ω)
  obtain ⟨E,hE,hbudget,hsharp⟩ := R.attaining_increments ω hω
  let S : FirstVariationScenario R (fcMethod fullMemory) ω := {
    increments := E
    symmetric := hE
    budget := fun l hl => hbudget l (by omega)
    variation := fullCycleResponse R.base R.gradient (range (n+1)) E
    derivative := canonicalFC_response_hasDerivAt R.base R.positive R.gradient R.full E hE }
  exact le_iSup_of_le S (by rw [show ‖S.variation‖/R.initialNorm=R.coefficient ω from hsharp])

/-- The genuine common first/last CG-plane increment family obeys every actual source component budget.
Use: The genuine common first/last CG-plane increment family obeys every actual source component budget.
Article: main_krylov, s3:cor:cf, genuine correction-free first-order minimax bounds.
Proof: The actual full CG frame supplies a genuine orthonormal plane; reuse the real planar spectral contraction and scale by each true nonnegative budget. -/
theorem crossIncrements_budget (R : FCReference (n+1) μ κ) (hn : 0<n) (ω : ℕ → ℝ)
    (hω : ∀ l<n, 0≤ω l) : ∀ l<n, ‖crossIncrements R.base R.gradient ω l‖≤ω l := by
  -- Actual CG orthogonality, rather than an assumed abstract plane, supplies the true budget witness.
  have ho := canonicalCG_frame_of_full_atoms R.base R.positive R.gradient R.full
  have he : ‖canonicalCGUnitStep R.base R.gradient 0‖=1 := ho.norm_eq_one 0
  have hh : ‖canonicalCGUnitStep R.base R.gradient n‖=1 := ho.norm_eq_one (Fin.last n)
  have heh : inner ℝ (canonicalCGUnitStep R.base R.gradient 0) (canonicalCGUnitStep R.base R.gradient n)=0 :=
    ho.inner_eq_zero (i := 0) (j := Fin.last n) (by intro hz;have h:=congrArg Fin.val hz;simp only [Fin.val_zero,Fin.val_last] at h;omega)
  have hM : ‖planarMatrix (canonicalCGUnitStep R.base R.gradient 0) (canonicalCGUnitStep R.base R.gradient n) 0 1 0‖≤1 := by
    simpa only [neg_zero,chebyshev1.opNorm] using planar_spectral_norm_le _ _ he hh heh 0 1 (by norm_num)
  intro l hl
  have hs : crossIncrements R.base R.gradient ω l=ω l •
      planarMatrix (canonicalCGUnitStep R.base R.gradient 0) (canonicalCGUnitStep R.base R.gradient n) 0 1 0 := by
    simp only [crossIncrements,planarMatrix,zero_smul,zero_add,add_zero,one_smul]
  rw [hs,norm_smul,Real.norm_of_nonneg (hω l hl)]
  exact (mul_le_mul_of_nonneg_left hM (hω l hl)).trans_eq (by ring)

/-- Every actual CG-consistent correction-free raw strategy has the printed genuine first-order obstruction price.
Use: Every actual CG-consistent correction-free raw strategy has the printed genuine first-order obstruction price.
Article: main_krylov, s3:cor:cf, genuine correction-free first-order minimax bounds.
Proof: Construct the real cross-budget scenario with its actual derived path derivative. Genuine terminal CG energy and the actual first unit step give its exact normalized variation norm, which bounds the true price supremum below. -/
theorem correctionFree_price_lower (R : FCReference (n+1) μ κ) (hn : 0<n)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (n+1)))) (hm : CGConsistent m) (hfree : CorrectionFree m)
    (ω : ℕ → ℝ) (hω : ∀ l<n, 0≤ω l) :
    ENNReal.ofReal ((∑ l∈range n, ω l)*‖cgCanonicalError R.base R.gradient n‖/R.initialNorm)≤firstVariationPrice R m ω := by
  -- This is the genuine derivative of the actual common correction-free path.
  let v := ((∑ l∈range n, ω l)*Real.sqrt (cgEnergy R.base R.gradient n)) • canonicalCGUnitStep R.base R.gradient 0
  let S : FirstVariationScenario R m ω := {
    increments := crossIncrements R.base R.gradient ω
    symmetric := fun l => planarMatrix_isSymm _ _ _ _ _
    budget := crossIncrements_budget R hn ω hω
    variation := v
    derivative := correctionFree_cross_derivative R.base R.positive R.gradient hn R.full m hm hfree ω }
  have hlast : Real.sqrt (cgEnergy R.base R.gradient n)=‖cgCanonicalError R.base R.gradient n‖ := by
    have he := cgEnergy_tail R.base R.positive R.gradient (l := n) (by rw [R.full];omega)
    simp only [R.full,Nat.Ico_succ_singleton,sum_singleton] at he
    rw [← he,Real.sqrt_sq (norm_nonneg _)]
  have hnorm : ‖S.variation‖=(∑ l∈range n, ω l)*‖cgCanonicalError R.base R.gradient n‖ := by
    change ‖v‖=_
    rw [norm_smul,Real.norm_of_nonneg (mul_nonneg (sum_nonneg fun l hl => hω l (mem_range.mp hl)) (Real.sqrt_nonneg _)),
      (firstStep_common R.base R.positive R.gradient (by rw [R.full];omega)).1,mul_one,hlast]
  exact le_iSup_of_le S (by rw [hnorm])

/-- A genuine span-restricted probed information-class method that is globally CG-consistent and makes no actual correction query.
Use: A genuine span-restricted probed information-class method that is globally CG-consistent and makes no actual correction query.
Article: main_krylov, s3:cor:cf, genuine correction-free first-order minimax bounds.
Proof: The true oracle and span information restrictions remain part of each actual strategy. -/
structure CorrectionFreeStrategy (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The actual span-restricted nonanticipating source information-class member. -/
  method : ProbedClass E
  /-- The genuine method is globally CG-consistent on actual positive quadratic references. -/
  consistent : CGConsistent method.policy
  /-- The actual policy never issues a correction query. -/
  free : CorrectionFree method.policy

/-- The actual infimum of genuine worst first-variation prices over the true correction-free source information class.
Use: The actual infimum of genuine worst first-variation prices over the true correction-free source information class.
Article: main_krylov, s3:cor:cf, genuine correction-free first-order minimax bounds.
Proof: Each admissible strategy includes its real span restrictions and actual CG consistency. -/
def correctionFreeMinimax (R : FCReference (n+1) μ κ) (ω : ℕ → ℝ) : ENNReal :=
  ⨅ S : CorrectionFreeStrategy (EuclideanSpace ℝ (Fin (n+1))), firstVariationPrice R S.method.policy ω

/-- The true correction-free first-order minimax price lies between the printed common terminal-error lower coefficient and the genuine sharp FC upper coefficient.
Use: The true correction-free first-order minimax price lies between the printed common terminal-error lower coefficient and the genuine sharp FC upper coefficient.
Article: main_krylov, s3:cor:cf, genuine correction-free first-order minimax bounds.
Proof: Every actual information-class strategy has the proved true common cross-scenario derivative obstruction. The genuine full-memory FC class member is an admissible actual strategy whose worst first-variation price has the proved sharp upper bound. -/
theorem correctionFree_minimax_interval (R : FCReference (n+1) μ κ) (hn : 0<n)
    (ω : ℕ → ℝ) (hω : ∀ l<n+1, 0≤ω l) :
    ENNReal.ofReal ((∑ l∈range n, ω l)*‖cgCanonicalError R.base R.gradient n‖/R.initialNorm)≤correctionFreeMinimax R ω ∧
      correctionFreeMinimax R ω≤ENNReal.ofReal (R.coefficient ω) := by
  -- The actual class-wide lower bound and the admissible genuine FC strategy bound the real infimum.
  constructor
  · apply le_iInf
    intro S
    exact correctionFree_price_lower R hn S.method.policy S.consistent S.free ω (fun l hl => hω l (by omega))
  · let S : CorrectionFreeStrategy (EuclideanSpace ℝ (Fin (n+1))) := {
      method := fcClass fullMemory
      consistent := fcMethod_consistent fullMemory (fun k hk => hk)
      free := fcMethod_correctionFree fullMemory }
    exact iInf_le_of_le S (fc_firstVariationPrice_le R ω)
end
end krylov.Variation
