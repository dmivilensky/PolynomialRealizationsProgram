import krylov.Functions.RFCCanonicalQuadratic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Article: main_krylov, thm:Htransfer, genuine bilinear RFC coefficient control.
Use: replace actual search/correction jets in the real quadratic coefficient
with a compact-uniform error retaining its additional small factor.
Source: the actual two linear frozen factors and continuous bilinear operator norms.
-/

namespace krylov.Functions
noncomputable section
open Matrix Set krylov.Reference krylov.Methods krylov.Stability krylov.Correction
  krylov.Envelope krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The genuine finite physical search-deviation coordinate, as a bounded linear map.
Article: main_krylov, thm:Htransfer. -/
def rfcSearchDeviationL (k i : ℕ) : RFCPhysicalData k →L[ℝ] Matrix (Fin (k+1)) (Fin (k+1)) ℝ := by
  classical
  exact if hi : i < k+1 then (ContinuousLinearMap.proj (⟨i,hi⟩ : Fin (k+1))) ∘L
    (ContinuousLinearMap.fst ℝ _ _) ∘L (symmetricScenarios (k+1) (k+2)).subtypeL else 0

/-- The genuine independent physical correction-deviation coordinate.
Article: main_krylov, thm:Htransfer. -/
def rfcCorrectionDeviationL (k i : ℕ) : RFCPhysicalData k →L[ℝ] Matrix (Fin (k+1)) (Fin (k+1)) ℝ := by
  classical
  exact if hi : i < k+2 then (ContinuousLinearMap.proj (⟨i,hi⟩ : Fin (k+2))) ∘L
    (ContinuousLinearMap.snd ℝ _ _) ∘L (symmetricScenarios (k+1) (k+2)).subtypeL else 0

/-- The real bounded search-coordinate map reads exactly its original zero-extended finite array.
Article: main_krylov, thm:Htransfer. -/
theorem rfcSearchDeviationL_apply (Θ : RFCPhysicalData k) (i : ℕ) :
    rfcSearchDeviationL k i Θ = matrixSequenceExtension (k+1) Θ.val.1 i := by
  by_cases hi : i < k+1 <;> simp [rfcSearchDeviationL, matrixSequenceExtension, hi]


/-- The true bounded correction-coordinate map has the same exact original-array dictionary.
Article: main_krylov, thm:Htransfer. -/
theorem rfcCorrectionDeviationL_apply (Θ : RFCPhysicalData k) (i : ℕ) :
    rfcCorrectionDeviationL k i Θ = matrixSequenceExtension (k+2) Θ.val.2 i := by
  by_cases hi : i < k+2 <;> simp [rfcCorrectionDeviationL, matrixSequenceExtension, hi]


/-- The actual frozen latest-model error factor is linear in the real physical deviations.
Article: main_krylov, thm:Htransfer. -/
def rfcPhysicalModelErrorL (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) :
    RFCPhysicalData k →L[ℝ] Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun Θ => Matrix.of fun i j => inner ℝ (referenceModelBasis base g k i)
      (cgOperator (rfcCorrectionDeviationL k k Θ-rfcSearchDeviationL k (k-(min i j).val) Θ)
        (referenceModelBasis base g k j))
    map_add' := by
      intro Θ Ξ
      ext i j
      simp only [Matrix.of_apply, map_add, add_sub_add_comm, cgOperator, _root_.add_apply,
        Matrix.add_apply, inner_add_right]
    map_smul' := by
      intro c Θ
      ext i j
      simp only [Matrix.of_apply, map_smul, ← smul_sub, cgOperator, _root_.smul_apply,
        inner_smul_right, smul_eq_mul, Matrix.smul_apply, RingHom.id_apply] }

/-- The actual frozen incoming factor is linear in the same genuine finite physical deviations.
Article: main_krylov, thm:Htransfer. -/
def rfcPhysicalIncomingL (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) : RFCPhysicalData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1)) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun Θ => frozenIncoming (cgOperator base) g (fun i => cgOperator (rfcSearchDeviationL k i Θ)) k
    map_add' := by
      intro Θ Ξ
      ext i
      refine Fin.cases (by simp [frozenIncoming]) (fun j => ?_) i
      simp only [frozenIncoming, map_add, cgOperator, add_sub_add_comm, _root_.add_apply,
        WithLp.ofLp_add, Pi.add_apply, Fin.cons_succ, inner_add_right]
    map_smul' := by
      intro c Θ
      ext i
      refine Fin.cases (by simp [frozenIncoming]) (fun j => ?_) i
      simp only [frozenIncoming, map_smul, cgOperator, ← smul_sub, _root_.smul_apply,
        WithLp.ofLp_smul, Pi.smul_apply, Fin.cons_succ, inner_smul_right, smul_eq_mul, RingHom.id_apply] }

-- Use the operator norm on the genuine curried codomain consistently.
local instance rfcPhysicalCurriedNormedAddCommGroup :
    NormedAddCommGroup (RFCPhysicalData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := RFCPhysicalData k) (F := EuclideanSpace ℝ (Fin (k+1)))
local instance rfcPhysicalCurriedNormedSpace :
    NormedSpace ℝ (RFCPhysicalData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := RFCPhysicalData k) (F := EuclideanSpace ℝ (Fin (k+1)))

local instance rfcPhysicalBilinearNormedAddCommGroup :
    NormedAddCommGroup (RFCPhysicalData k →L[ℝ] RFCPhysicalData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := RFCPhysicalData k) (F := RFCPhysicalData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
local instance rfcPhysicalBilinearNormedSpace :
    NormedSpace ℝ (RFCPhysicalData k →L[ℝ] RFCPhysicalData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := RFCPhysicalData k) (F := RFCPhysicalData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))

set_option maxHeartbeats 800000 in
/-- The actual physical RFC quadratic coefficient is the diagonal of this genuine bounded bilinear map.
Article: main_krylov, thm:Htransfer.
Use: true multilinear norm control handles arbitrary actual little-o jets and quadratic jets. -/
def rfcPhysicalBilinear (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) : RFCPhysicalData k →L[ℝ] RFCPhysicalData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1)) :=
  let U := referenceModelBasis base g k
  let H := pairModel U (fun i => cgOperator base (U i))
  let R := fullBasisMatrix U
  let L := rfcPhysicalModelErrorL base g
  let V := rfcPhysicalIncomingL base g
  LinearMap.toContinuousLinearMap {
    toFun := fun Θ => LinearMap.toContinuousLinearMap {
      toFun := fun Ξ => cgOperator (Rᵀ⁻¹ * (L Θ * H⁻¹)) (V Ξ)
      map_add' := by intro Ξ Ψ; rw [map_add, map_add]
      map_smul' := by intro c Ξ; simp only [map_smul, RingHom.id_apply] }
    map_add' := by
      intro Θ Ξ
      apply ContinuousLinearMap.ext
      intro Ψ
      change cgOperator (Rᵀ⁻¹ * (L (Θ+Ξ) * H⁻¹)) (V Ψ) =
        cgOperator (Rᵀ⁻¹ * (L Θ * H⁻¹)) (V Ψ) + cgOperator (Rᵀ⁻¹ * (L Ξ * H⁻¹)) (V Ψ)
      rw [map_add, Matrix.add_mul, Matrix.mul_add]
      simp only [cgOperator, map_add, _root_.add_apply]
    map_smul' := by
      intro c Θ
      apply ContinuousLinearMap.ext
      intro Ξ
      change cgOperator (Rᵀ⁻¹ * (L (c • Θ) * H⁻¹)) (V Ξ) =
        c • cgOperator (Rᵀ⁻¹ * (L Θ * H⁻¹)) (V Ξ)
      rw [map_smul, Matrix.smul_mul, Matrix.mul_smul]
      simp only [cgOperator, map_smul, _root_.smul_apply] }

/-- The true physical two-factor formula agrees exactly with the real RFC coefficient on the diagonal.
Article: main_krylov, thm:Htransfer.
Proof: cancel the actual shared base in each model-error and incoming operator difference. -/
theorem rfcPhysicalBilinear_diagonal (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) (Θ : RFCPhysicalData k) :
    rfcPhysicalBilinear base g Θ Θ =
      rfcPhysicalQuadratic base g (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ) := by
  simp only [rfcPhysicalBilinear, rfcPhysicalQuadratic, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk, rfcPhysicalModelErrorL, rfcPhysicalIncomingL,
    rfcPhysicalSearch, rfcPhysicalCorrection, rfcSearchDeviationL_apply, rfcCorrectionDeviationL_apply,
    frozenIncoming, cgOperator, map_add, add_sub_add_left_eq_sub, ← map_sub]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The genuine coefficient difference retains one small jet-size factor.
Article: main_krylov, thm:Htransfer, homogeneous substitution estimate.
Proof: split the true bilinear diagonal difference and apply its actual bounded bilinear norm twice. -/
theorem rfcPhysicalBilinear_difference_bound (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) (Θ Ξ : RFCPhysicalData k) :
    ‖rfcPhysicalBilinear base g Θ Θ-rfcPhysicalBilinear base g Ξ Ξ‖ ≤
      ‖rfcPhysicalBilinear base g‖ * (‖Θ‖+‖Ξ‖) * ‖Θ-Ξ‖ := by
  let B := rfcPhysicalBilinear base g
  have he : B Θ Θ-B Ξ Ξ = B Θ (Θ-Ξ)+B (Θ-Ξ) Ξ := by simp only [map_sub, _root_.sub_apply]; abel
  rw [he]
  have hB₁ : ‖B Θ‖ ≤ ‖B‖ * ‖Θ‖ := by convert! ContinuousLinearMap.le_opNorm B Θ
  have hB₂ : ‖B (Θ-Ξ)‖ ≤ ‖B‖ * ‖Θ-Ξ‖ := by convert! ContinuousLinearMap.le_opNorm B (Θ-Ξ)
  have h₁ := ((B Θ).le_opNorm (Θ-Ξ)).trans
    (mul_le_mul_of_nonneg_right hB₁ (norm_nonneg _))
  have h₂ := ((B (Θ-Ξ)).le_opNorm Ξ).trans
    (mul_le_mul_of_nonneg_right hB₂ (norm_nonneg _))
  exact (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

set_option maxHeartbeats 800000 in
/-- Every actual bilinear coefficient evaluation is analytic on the true nonstagnating reference domain.
Article: main_krylov, thm:Htransfer and lem:U.
Proof: the genuine reference basis and its true invertible model matrices
are analytic; both independent frozen factors use their actual linear query coordinates. -/
theorem rfcPhysicalBilinear_analyticAt
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hpre : ∀ i ≤ k, CG.gradient (cgOperator base) g i ≠ 0)
    (Θ Ξ : RFCPhysicalData k) :
    AnalyticAt ℝ (fun p => rfcPhysicalBilinear base p Θ Ξ) g := by
  let U := fun p => referenceModelBasis base p k
  let H := fun p => pairModel (U p) (fun i => cgOperator base (U p i))
  let R := fun p => fullBasisMatrix (U p)
  let L := fun p => Matrix.of fun i j : Fin (k+1) => inner ℝ (U p i)
    (cgOperator (rfcCorrectionDeviationL k k Θ-rfcSearchDeviationL k (k-(min i j).val) Θ) (U p j))
  have hd := reference_model_data_analyticAt (fun _ : EuclideanSpace ℝ (Fin (k+1)) => base)
    (fun p => p) g analyticAt_const hb analyticAt_id hpre
  have hL : AnalyticAt ℝ L g := analytic_spectral_matrix _ g fun i j =>
    analytic_inner (hd.1 i) (analytic_operator_apply analyticAt_const (hd.1 j))
  have hHi : AnalyticAt ℝ (fun p => (H p)⁻¹) g := analytic_spectral_matrix_inv H g
    (fun i j => analytic_matrix_entry hd.2.1 i j) (isUnit_iff_ne_zero.mp hd.2.2.2.1)
  have hRi : AnalyticAt ℝ (fun p => (R p)ᵀ⁻¹) g := analytic_spectral_matrix_inv _ g
    (fun i j => analytic_matrix_entry hd.2.2.1 j i)
    (by simpa only [det_transpose] using isUnit_iff_ne_zero.mp hd.2.2.2.2)
  have hr := frozenIncoming_variable_analyticAt
    (fun _ : EuclideanSpace ℝ (Fin (k+1)) => cgOperator base) (fun p => p)
    (fun _ i => cgOperator (rfcSearchDeviationL k i Ξ)) g analyticAt_const analyticAt_id
    (fun _ => analyticAt_const) (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 k hpre
  exact analytic_operator_apply
    (matrixOperator_contDiffAt _ g (hRi.mul (hL.mul hHi)).contDiffAt).analyticAt hr

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The true bounded bilinear coefficient has a uniform operator norm on every genuine compact reference family.
Article: main_krylov, thm:Htransfer and lem:U.
Proof: finite dimensional pointwise continuity gives continuity in the
actual bounded bilinear norm; compactness supplies its bound. -/
theorem compact_rfcPhysicalBilinear_norm
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i ≤ k, CG.gradient (cgOperator base) g i ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g ∈ K, ‖rfcPhysicalBilinear base g‖ ≤ M := by
  have hc : ContinuousOn (rfcPhysicalBilinear base) K := by
    apply continuousOn_clm_apply.mpr
    intro Θ
    apply continuousOn_clm_apply.mpr
    intro Ξ g hg
    exact (rfcPhysicalBilinear_analyticAt base hb g (hpre g hg) Θ Ξ).continuousAt.continuousWithinAt
  have hn : ContinuousOn (fun g => ‖rfcPhysicalBilinear base g‖) K := by
    apply ContinuousOn.norm
    convert! hc
  obtain ⟨M,hM⟩ := hK.bddAbove_image hn
  exact ⟨max M 0,le_max_right _ _,fun g hg => (hM ⟨g,hg,rfl⟩).trans (le_max_left _ _)⟩

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- A compact-uniform genuine quadratic substitution estimate for the actual physical RFC coefficient.
Article: main_krylov, thm:Htransfer.
Use: first-order true query jets give the cubic tensor response; quadratic
query remainders give a fourth-order true function remainder. -/
theorem compact_rfcPhysicalQuadratic_difference
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i ≤ k, CG.gradient (cgOperator base) g i ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g ∈ K, ∀ Θ Ξ : RFCPhysicalData k,
      ‖rfcPhysicalQuadratic base g (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ)-
        rfcPhysicalQuadratic base g (rfcPhysicalSearch base Ξ) (rfcPhysicalCorrection base Ξ)‖ ≤
        M*(‖Θ‖+‖Ξ‖)*‖Θ-Ξ‖ := by
  obtain ⟨M,hM,hbound⟩ := compact_rfcPhysicalBilinear_norm base hb K hK hpre
  refine ⟨M,hM,fun g hg Θ Ξ => ?_⟩
  rw [← rfcPhysicalBilinear_diagonal,← rfcPhysicalBilinear_diagonal]
  exact (rfcPhysicalBilinear_difference_bound base g Θ Ξ).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hbound g hg) (by positivity)) (norm_nonneg _))

end
end krylov.Functions
