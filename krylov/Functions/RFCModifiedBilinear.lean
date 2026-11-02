import krylov.Functions.RFCModifiedPhysical

/-!
Article: main_krylov, prop:Fcycle(i), genuine corrected-model coefficient control.
Use: place the actual operator source and the independent last-model change
in one finite normed source space. The exact corrected physical coefficient
is a bounded bilinear diagonal, with a compact uniform substitution bound.
Source: the two genuine linear frozen factors and bounded bilinear norms.
-/

namespace krylov.Functions
noncomputable section
open Matrix Set krylov.Reference krylov.Methods krylov.Stability krylov.Correction
  krylov.Envelope krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The true corrected physical source: original symmetric operator deviations and an arbitrary independent final model change.
Article: main_krylov, prop:Fcycle(i), the genuine joint source norm. -/
abbrev RFCModifiedData (k : ℕ) :=
  RFCPhysicalData k × Matrix (Fin (k+1)) (Fin (k+1)) ℝ

local instance modifiedCurriedNormedAddCommGroup :
    NormedAddCommGroup (RFCModifiedData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := RFCModifiedData k) (F := EuclideanSpace ℝ (Fin (k+1)))
local instance modifiedCurriedNormedSpace :
    NormedSpace ℝ (RFCModifiedData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := RFCModifiedData k) (F := EuclideanSpace ℝ (Fin (k+1)))
local instance modifiedBilinearNormedAddCommGroup :
    NormedAddCommGroup (RFCModifiedData k →L[ℝ] RFCModifiedData k →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1))) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := RFCModifiedData k) (F := RFCModifiedData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
local instance modifiedBilinearNormedSpace :
    NormedSpace ℝ (RFCModifiedData k →L[ℝ] RFCModifiedData k →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1))) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := RFCModifiedData k) (F := RFCModifiedData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))

/-- The actual corrected physical coefficient is the diagonal of this genuine bounded bilinear map.
Article: main_krylov, prop:Fcycle(i), the factor (L-Delta_H) times the fresh defect. -/
def rfcModifiedBilinear (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) :
    RFCModifiedData k →L[ℝ] RFCModifiedData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1)) :=
  let U := referenceModelBasis base g k
  let H := pairModel U (fun i => cgOperator base (U i))
  let R := fullBasisMatrix U
  let L : RFCModifiedData k →L[ℝ] Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
    (rfcPhysicalModelErrorL base g).comp (ContinuousLinearMap.fst ℝ _ _) - ContinuousLinearMap.snd ℝ _ _
  let V : RFCModifiedData k →L[ℝ] EuclideanSpace ℝ (Fin (k+1)) :=
    (rfcPhysicalIncomingL base g).comp (ContinuousLinearMap.fst ℝ _ _)
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

/-- The actual corrected physical formula is exactly the genuine bilinear diagonal.
Article: main_krylov, prop:Fcycle(i), with the original independent model change. -/
theorem rfcModifiedBilinear_diagonal (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) (Θ : RFCPhysicalData k)
    (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) :
    rfcModifiedBilinear base g (Θ,D) (Θ,D) =
      rfcModifiedQuadratic base g (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ) D := by
  simp only [rfcModifiedBilinear, rfcModifiedQuadratic, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk, rfcPhysicalModelErrorL, rfcPhysicalIncomingL,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    _root_.sub_apply, rfcPhysicalSearch, rfcPhysicalCorrection, rfcSearchDeviationL_apply,
    rfcCorrectionDeviationL_apply, frozenIncoming, cgOperator, map_add,
    add_sub_add_left_eq_sub, ← map_sub]

/-- The real corrected physical coefficient has exact degree two in its full operator/model source.
Article: main_krylov, prop:Fcycle(i), joint homogeneous substitution. -/
theorem rfcModifiedQuadratic_source_smul (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) (Θ : RFCPhysicalData k)
    (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (c : ℝ) :
    rfcModifiedQuadratic base g (rfcPhysicalSearch base (c • Θ)) (rfcPhysicalCorrection base (c • Θ)) (c • D) =
      c ^ 2 • rfcModifiedQuadratic base g (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ) D := by
  rw [← rfcModifiedBilinear_diagonal, ← rfcModifiedBilinear_diagonal]
  change rfcModifiedBilinear base g (c • (Θ,D)) (c • (Θ,D)) =
    c ^ 2 • rfcModifiedBilinear base g (Θ,D) (Θ,D)
  rw [map_smul, map_smul]
  change c • (c • rfcModifiedBilinear base g (Θ,D) (Θ,D)) = _
  rw [smul_smul]
  congr 1
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The genuine corrected bilinear response retains an additional small source factor in every diagonal difference.
Article: main_krylov, prop:Fcycle(i), the exact jet substitution estimate. -/
theorem rfcModifiedBilinear_difference_bound (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) (Θ Ξ : RFCModifiedData k) :
    ‖rfcModifiedBilinear base g Θ Θ - rfcModifiedBilinear base g Ξ Ξ‖ ≤
      ‖rfcModifiedBilinear base g‖ * (‖Θ‖ + ‖Ξ‖) * ‖Θ-Ξ‖ := by
  let B := rfcModifiedBilinear base g
  have he : B Θ Θ - B Ξ Ξ = B Θ (Θ-Ξ) + B (Θ-Ξ) Ξ := by
    simp only [map_sub, _root_.sub_apply]
    abel
  rw [he]
  have hB₁ : ‖B Θ‖ ≤ ‖B‖ * ‖Θ‖ := by convert! ContinuousLinearMap.le_opNorm B Θ
  have hB₂ : ‖B (Θ-Ξ)‖ ≤ ‖B‖ * ‖Θ-Ξ‖ := by convert! ContinuousLinearMap.le_opNorm B (Θ-Ξ)
  have h₁ := ((B Θ).le_opNorm (Θ-Ξ)).trans
    (mul_le_mul_of_nonneg_right hB₁ (norm_nonneg _))
  have h₂ := ((B (Θ-Ξ)).le_opNorm Ξ).trans
    (mul_le_mul_of_nonneg_right hB₂ (norm_nonneg _))
  exact (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

/-- Every genuine corrected bilinear evaluation is analytic in the actual nonstagnating reference gradient.
Article: main_krylov, prop:Fcycle(i), common compact response regularity. -/
theorem rfcModifiedBilinear_analyticAt
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hpre : ∀ i ≤ k, CG.gradient (cgOperator base) g i ≠ 0)
    (Θ Ξ : RFCModifiedData k) :
    AnalyticAt ℝ (fun p => rfcModifiedBilinear base p Θ Ξ) g := by
  let U := fun p => referenceModelBasis base p k
  let H := fun p => pairModel (U p) (fun i => cgOperator base (U p i))
  let R := fun p => fullBasisMatrix (U p)
  let L := fun p => (Matrix.of fun i j : Fin (k+1) => inner ℝ (U p i)
    (cgOperator (rfcCorrectionDeviationL k k Θ.1 - rfcSearchDeviationL k (k-(min i j).val) Θ.1) (U p j))) - Θ.2
  have hd := reference_model_data_analyticAt (fun _ : EuclideanSpace ℝ (Fin (k+1)) => base)
    (fun p => p) g analyticAt_const hb analyticAt_id hpre
  have hL : AnalyticAt ℝ L g := analytic_spectral_matrix _ g fun i j =>
    (analytic_inner (hd.1 i) (analytic_operator_apply analyticAt_const (hd.1 j))).sub analyticAt_const
  have hHi : AnalyticAt ℝ (fun p => (H p)⁻¹) g := analytic_spectral_matrix_inv H g
    (fun i j => analytic_matrix_entry hd.2.1 i j) (isUnit_iff_ne_zero.mp hd.2.2.2.1)
  have hRi : AnalyticAt ℝ (fun p => (R p)ᵀ⁻¹) g := analytic_spectral_matrix_inv _ g
    (fun i j => analytic_matrix_entry hd.2.2.1 j i)
    (by simpa only [det_transpose] using isUnit_iff_ne_zero.mp hd.2.2.2.2)
  have hr := frozenIncoming_variable_analyticAt
    (fun _ : EuclideanSpace ℝ (Fin (k+1)) => cgOperator base) (fun p => p)
    (fun _ i => cgOperator (rfcSearchDeviationL k i Ξ.1)) g analyticAt_const analyticAt_id
    (fun _ => analyticAt_const) (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 k hpre
  exact analytic_operator_apply
    (matrixOperator_contDiffAt _ g (hRi.mul (hL.mul hHi)).contDiffAt).analyticAt hr

set_option backward.isDefEq.respectTransparency false in
/-- The true corrected bounded bilinear response has a compact-uniform operator norm.
Article: main_krylov, prop:Fcycle(i), joint original-source control. -/
theorem compact_rfcModifiedBilinear_norm
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i ≤ k, CG.gradient (cgOperator base) g i ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g ∈ K, ‖rfcModifiedBilinear base g‖ ≤ M := by
  have hc : ContinuousOn (rfcModifiedBilinear base) K := by
    apply continuousOn_clm_apply.mpr
    intro Θ
    apply continuousOn_clm_apply.mpr
    intro Ξ g hg
    exact (rfcModifiedBilinear_analyticAt base hb g (hpre g hg) Θ Ξ).continuousAt.continuousWithinAt
  have hn : ContinuousOn (fun g => ‖rfcModifiedBilinear base g‖) K := by
    apply ContinuousOn.norm
    convert! hc
  obtain ⟨M, hM⟩ := hK.bddAbove_image hn
  exact ⟨max M 0, le_max_right _ _, fun g hg => (hM ⟨g,hg,rfl⟩).trans (le_max_left _ _)⟩

set_option backward.isDefEq.respectTransparency false in
/-- A compact-uniform quadratic substitution estimate for the actual corrected physical coefficient.
Article: main_krylov, prop:Fcycle(i), substitution of actual operator and diagonal jets. -/
theorem compact_rfcModifiedQuadratic_difference
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i ≤ k, CG.gradient (cgOperator base) g i ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g ∈ K, ∀ Θ Ξ : RFCModifiedData k,
      ‖rfcModifiedQuadratic base g (rfcPhysicalSearch base Θ.1) (rfcPhysicalCorrection base Θ.1) Θ.2 -
        rfcModifiedQuadratic base g (rfcPhysicalSearch base Ξ.1) (rfcPhysicalCorrection base Ξ.1) Ξ.2‖ ≤
      M * (‖Θ‖ + ‖Ξ‖) * ‖Θ-Ξ‖ := by
  obtain ⟨M, hM, hbound⟩ := compact_rfcModifiedBilinear_norm base hb K hK hpre
  refine ⟨M, hM, fun g hg Θ Ξ => ?_⟩
  rw [← rfcModifiedBilinear_diagonal, ← rfcModifiedBilinear_diagonal]
  exact (rfcModifiedBilinear_difference_bound base g Θ Ξ).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hbound g hg) (by positivity)) (norm_nonneg _))

set_option backward.isDefEq.respectTransparency false in
/-- The actual corrected physical coefficient has a genuine compact-uniform quadratic source bound.
Article: main_krylov, prop:Fcycle(ii), the quantitative cycle-order input. -/
theorem compact_rfcModifiedQuadratic_norm
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i ≤ k, CG.gradient (cgOperator base) g i ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g ∈ K, ∀ Θ : RFCModifiedData k,
      ‖rfcModifiedQuadratic base g (rfcPhysicalSearch base Θ.1) (rfcPhysicalCorrection base Θ.1) Θ.2‖ ≤
        M * ‖Θ‖ ^ 2 := by
  obtain ⟨M, hM, hbound⟩ := compact_rfcModifiedBilinear_norm base hb K hK hpre
  refine ⟨M, hM, fun g hg Θ => ?_⟩
  rw [← rfcModifiedBilinear_diagonal]
  let B := rfcModifiedBilinear base g
  have hB : ‖B Θ‖ ≤ ‖B‖ * ‖Θ‖ := by convert! ContinuousLinearMap.le_opNorm B Θ
  have hh := ((B Θ).le_opNorm Θ).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  apply hh.trans
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hbound g hg) (norm_nonneg Θ)) (norm_nonneg Θ)).trans_eq (by ring)

/-- True operator/model first jets enter the actual corrected quadratic response with one additional source-scale factor.
Article: main_krylov, prop:Fcycle(i), the compact native coefficient substitution.
All response regularity and its common constant are derived from the true
bounded bilinear map, so no coefficient-continuity estimate is a premise. -/
theorem compact_rfcModifiedQuadratic_jet
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i ≤ k, CG.gradient (cgOperator base) g i ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g ∈ K, ∀ Θ Ω : RFCModifiedData k,
      ∀ ε D W J : ℝ, 0 ≤ ε → 0 ≤ D → 0 ≤ W → 0 ≤ J →
      ‖Θ‖ ≤ D * ε → ‖Ω‖ ≤ W → ‖Θ - ε • Ω‖ ≤ J →
      ‖rfcModifiedQuadratic base g (rfcPhysicalSearch base Θ.1) (rfcPhysicalCorrection base Θ.1) Θ.2 -
        ε ^ 2 • rfcModifiedQuadratic base g (rfcPhysicalSearch base Ω.1) (rfcPhysicalCorrection base Ω.1) Ω.2‖ ≤
        M * (D + W) * ε * J := by
  obtain ⟨M, hM, hdiff⟩ := compact_rfcModifiedQuadratic_difference base hb K hK hpre
  refine ⟨M, hM, ?_⟩
  intro g hg Θ Ω ε D W J hε hD hW _ hΘ hΩ hjet
  have hh := hdiff g hg Θ (ε • Ω)
  change ‖rfcModifiedQuadratic base g (rfcPhysicalSearch base Θ.1) (rfcPhysicalCorrection base Θ.1) Θ.2 -
    rfcModifiedQuadratic base g (rfcPhysicalSearch base (ε • Ω.1)) (rfcPhysicalCorrection base (ε • Ω.1)) (ε • Ω.2)‖ ≤
      M * (‖Θ‖ + ‖ε • Ω‖) * ‖Θ - ε • Ω‖ at hh
  rw [rfcModifiedQuadratic_source_smul] at hh
  have hΩε : ‖ε • Ω‖ ≤ ε * W := by
    rw [norm_smul, Real.norm_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left hΩ hε
  exact hh.trans ((mul_le_mul
    (mul_le_mul_of_nonneg_left (add_le_add hΘ hΩε) hM) hjet (norm_nonneg _) (by positivity)).trans_eq (by ring))

end
end krylov.Functions
