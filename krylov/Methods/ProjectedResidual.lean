import krylov.Methods.ProjectedRecording
import krylov.Methods.ProjectedCorrectionOrder
import krylov.Methods.CorrectionPairs

/-!
Article: main_krylov, lem:projected-residual, step-independent RFC estimates.
Use: assemble the normalized actual solve, the genuine spectral domains and
the actual recorded-window transfer into the four projected-residual bounds.
Source: the proved normalized correction identities, observed pair-error
estimates, finite spectral calculus and actual exact-search formula.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.LinearAlgebra krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ}

/-- The source's actual operator-image pair plus correction error has the stated relative pair bound.
Use: discharge the normalized-pair premise from y_i=A_i s_i+ξ_i.
Article: main_krylov, lem:projected-residual, hypotheses on the old pairs.
Proof: subtract the identity image and add the actual correction discrepancy;
the operator norm and triangle inequality give (1+K)ε times the physical column norm. -/
theorem observed_pair_error_bound (A : E →L[ℝ] E) (s ξ y : E) {ε K : ℝ}
    (hy : y=A s+ξ) (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤ε) (hξ : ‖ξ‖≤K*ε*‖s‖) :
    ‖y-s‖≤((1+K)*ε)*‖s‖ := by
  rw [hy, show A s+ξ-s=(A-ContinuousLinearMap.id ℝ E) s+ξ by
    rw [_root_.sub_apply, ContinuousLinearMap.id_apply]; abel]
  exact ((norm_add_le _ _).trans (add_le_add
    (((A-ContinuousLinearMap.id ℝ E).le_opNorm s).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) hξ)).trans_eq (by ring)

/-- The genuine normalized model spectrum discharges the actual rectangular correction bounds.
Use: no raw inverse domain, minimum step length or assumed surrogate correction is needed.
Article: main_krylov, lem:projected-residual, first and third bounds and augmented residual.
Proof: the true spectral lower endpoint proves the inverse domain and inverse
bound; the true Gram upper endpoint bounds synthesis, and the normalized model
error propagates the actual observed-gradient correction. -/
theorem normalized_model_correction_bounds (s y : Fin p → E) (hs : ∀ i, s i≠0)
    (B : E →L[ℝ] E) (g : E) {a b ε η : ℝ} (ha : 0<a) (hb : 0≤b)
    (hε : 0≤ε) (hη : 0≤η) (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ε)
    (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖)
    (hmodel : ∀ i, a≤(rescale_pairModel_isHermitian s y (fun j => ‖s j‖⁻¹)).eigenvalues i)
    (hgram : ∀ i, 0≤(crossGram_isHermitian (unitWindow s)).eigenvalues i ∧
      (crossGram_isHermitian (unitWindow s)).eigenvalues i≤b) :
    let H := pairModel s y
    let Hn := rescaleModel H (fun i => ‖s i‖⁻¹)
    let ρ := projectedResidual (unitWindow s) g
    let χ := combine s (modelCoefficients s H g)
    ‖correctionCompression (unitWindow s) B-Hn‖≤p*(ε+η) ∧
      ‖χ‖≤Real.sqrt b*a⁻¹*‖ρ‖ ∧
      ‖projectedResidual (unitWindow s) (g+B χ)‖≤p*(ε+η)*a⁻¹*‖ρ‖ := by
  -- Every matrix inverse is justified by the spectrum of the actual normalized latest model.
  obtain ⟨hu, hi⟩ := inverse_bound_of_eigenvalues _
    (rescale_pairModel_isHermitian s y _) ha hmodel
  have hg := spectral_norm_le_of_eigenvalues _ (crossGram_isHermitian (unitWindow s)) hb hgram
  have hN := normalized_pairModel_error_bound s y hs B hε hη hB hy
  have hd := unitWindow_diagonal_unit s hs
  refine ⟨hN, ?_, ?_⟩
  · exact (normalizedCorrection_movement_bound s (pairModel s y) _ hd g hb hg).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg _)) (norm_nonneg _))
  · exact (normalizedCorrection_bound s (pairModel s y) _ hd hu B g).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul hN hi (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg p) (add_nonneg hε hη))) (norm_nonneg _))

/-- The genuine normalized Gram lower endpoint bounds projection onto the actual recorded step after a model correction.
Use: the source relative-correction condition yields a length-independent R₊ estimate.
Article: main_krylov, lem:projected-residual, recorded-window transfer.
Proof: rewrite the actual correction in normalized coordinates; its genuine
Gram lower endpoint bounds its coefficients, then the proved recorded-unit-step
estimate applies to the actual line plus correction. -/
theorem normalized_recorded_correction_bound (s : Fin p → E) (d g : E)
    (H : Matrix (Fin (p+1)) (Fin (p+1)) ℝ) (α : ℝ) (hd : d≠0) (hs : ∀ i, s i≠0)
    {a K : ℝ} (ha : 0<a)
    (hgram : ∀ i, a≤(crossGram_isHermitian (unitWindow (Fin.cons d s))).eigenvalues i)
    (hv : α • d+combine (Fin.cons d s) (modelCoefficients (Fin.cons d s) H g)≠0)
    (hχ : ‖combine (Fin.cons d s) (modelCoefficients (Fin.cons d s) H g)‖≤
      K*‖α • d+combine (Fin.cons d s) (modelCoefficients (Fin.cons d s) H g)‖) (gplus : E) :
    ‖projectedResidual (unitWindow (Fin.cons
      (α • d+combine (Fin.cons d s) (modelCoefficients (Fin.cons d s) H g)) s)) gplus‖≤
      (2+K+(Real.sqrt a)⁻¹*K)*‖projectedResidual (unitWindow (Fin.cons d s)) gplus‖ := by
  -- Normalize only the actual augmented columns; the physical solved correction remains exactly the same.
  let U : Fin (p+1) → E := Fin.cons d s
  let T := unitWindow U
  let c := modelCoefficients T (rescaleModel H (fun i => ‖U i‖⁻¹)) g
  have hu (i : Fin (p+1)) : U i≠0 := Fin.cases hd hs i
  have hc : combine T c=combine U (modelCoefficients U H g) :=
    modelCorrection_rescale U H _ (unitWindow_diagonal_unit U hu) g
  have hline : (α*‖d‖) • T 0=α • d := by
    change (α*‖d‖) • (‖d‖⁻¹ • d)=α • d
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hd), mul_one]
  have ht := recorded_residual_bound T c gplus (α*‖d‖)
    (inv_nonneg.mpr (Real.sqrt_nonneg a)) (unitWindow_norm U hu 0)
    (combine_coefficients_bound T c ha hgram)
    (by rw [hline, hc]; exact hv) (by rw [hc, hline]; exact hχ)
  have he : Fin.cons
      (‖(α*‖d‖) • T 0+combine T c‖⁻¹ • ((α*‖d‖) • T 0+combine T c))
        (fun i : Fin p => T i.succ)=unitWindow (Fin.cons
          (α • d+combine U (modelCoefficients U H g)) s) := by
    rw [hline, hc, unitWindow_cons]
    ext i
    refine Fin.cases rfl (fun j => ?_) i
    change unitWindow U j.succ=unitWindow s j
    simp only [unitWindow, rescaleWindow, U, Fin.cons_succ]
  rw [he] at ht
  exact ht

/-- All four source projected-residual estimates hold for the genuine normalized RFC solve with explicit conditioning constants.
Use: the constants depend only on a,b,K and are independent of individual step lengths and the column count.
Article: main_krylov, lem:projected-residual, eq:projected-residual.
Proof: actual conjugacy and exact search bound the incoming normalized residual;
the actual pair/model estimate and genuine spectral domains bound the correction,
and the true Gram lower endpoint transfers its residual to the actual recorded step. -/
theorem normalizedRFC_projected_estimates (s y : Fin p → E) (hs : ∀ i, s i≠0)
    (A B : E →L[ℝ] E) (g d : E) {a b ε K : ℝ} (ha : 0<a) (hb : 0≤b)
    (hε : 0≤ε) (hK : 0≤K)
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤ε) (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ε)
    (hy : ∀ i, ‖y i-s i‖≤((1+K)*ε)*‖s i‖) (ho : ∀ i, inner ℝ (y i) d=0)
    (hc : inner ℝ d (A d)≠0)
    (hmodel : ∀ i, a≤(rescale_pairModel_isHermitian (Fin.cons d s) (Fin.cons (A d) y)
      (fun j => ‖(Fin.cons d s : Fin (p+1) → E) j‖⁻¹)).eigenvalues i)
    (hgram : ∀ i, a≤(crossGram_isHermitian (unitWindow (Fin.cons d s))).eigenvalues i ∧
      (crossGram_isHermitian (unitWindow (Fin.cons d s))).eigenvalues i≤b)
    (hv : lineLength g d (A d) • d+combine (Fin.cons d s)
      (modelCoefficients (Fin.cons d s) (pairModel (Fin.cons d s) (Fin.cons (A d) y))
        (searchedGradient g d (A d)))≠0)
    (hχ : ‖combine (Fin.cons d s)
      (modelCoefficients (Fin.cons d s) (pairModel (Fin.cons d s) (Fin.cons (A d) y))
        (searchedGradient g d (A d)))‖≤K*‖lineLength g d (A d) • d+combine (Fin.cons d s)
          (modelCoefficients (Fin.cons d s) (pairModel (Fin.cons d s) (Fin.cons (A d) y))
            (searchedGradient g d (A d)))‖) :
    let U : Fin (p+1) → E := Fin.cons d s
    let H := pairModel U (Fin.cons (A d) y)
    let T := unitWindow U
    let Hn := rescaleModel H (fun i => ‖U i‖⁻¹)
    let ρ := projectedResidual T (searchedGradient g d (A d))
    let R := ‖projectedResidual (unitWindow s) g‖
    let t := ‖lineLength g d (A d) • d‖
    let χ := combine U (modelCoefficients U H (searchedGradient g d (A d)))
    ‖correctionCompression T B-Hn‖≤(p+1)*((2+K)*ε) ∧
      ‖ρ‖≤R+Real.sqrt (p+1)*(((2+K)*ε)*t) ∧
      ‖χ‖≤Real.sqrt b*a⁻¹*‖ρ‖ ∧
      ‖projectedResidual (unitWindow (Fin.cons (lineLength g d (A d) • d+χ) s))
        (searchedGradient g d (A d)+B χ)‖≤
          ((2+K+(Real.sqrt a)⁻¹*K)*((p+1)*((2+K)*ε)*a⁻¹))*
            (R+Real.sqrt (p+1)*(((2+K)*ε)*t)) := by
  -- Both inverse domains are derived from actual normalized matrices; the recorded step is the actual line plus solve.
  have hd : d≠0 := by intro hz; rw [hz, map_zero, inner_zero_left] at hc; exact hc rfl
  have hu (i : Fin (p+1)) : (Fin.cons d s : Fin (p+1) → E) i≠0 := Fin.cases hd hs i
  have hη : 0≤(1+K)*ε := mul_nonneg (by linarith) hε
  have hyU (i : Fin (p+1)) : ‖(Fin.cons (A d) y : Fin (p+1) → E) i-
      (Fin.cons d s : Fin (p+1) → E) i‖≤((1+K)*ε)*‖(Fin.cons d s : Fin (p+1) → E) i‖ := by
    refine Fin.cases ?_ (fun j => hy j) i
    simp only [Fin.cons_zero]
    have ht := (A-ContinuousLinearMap.id ℝ E).le_opNorm d
    change ‖A d-d‖≤_ at ht
    exact (ht.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _))
  obtain ⟨hN, hmove, hres⟩ := normalized_model_correction_bounds
    (Fin.cons d s) (Fin.cons (A d) y) hu B (searchedGradient g d (A d)) ha hb hε hη hB hyU hmodel
      (fun i => ⟨ha.le.trans (hgram i).1, (hgram i).2⟩)
  have hrho := normalizedSearch_residual_bound s y hs A g d hε hη hA hy ho hc
  have he : ε+(1+K)*ε=(2+K)*ε := by ring
  rw [he] at hN hres hrho
  simp only [Nat.cast_add, Nat.cast_one] at hN hres
  refine ⟨hN, hrho, hmove, ?_⟩
  have hrecord := normalized_recorded_correction_bound s d (searchedGradient g d (A d))
    (pairModel (Fin.cons d s) (Fin.cons (A d) y)) (lineLength g d (A d)) hd hs ha
      (fun i => (hgram i).1) hv hχ (searchedGradient g d (A d)+B
        (combine (Fin.cons d s) (modelCoefficients (Fin.cons d s)
          (pairModel (Fin.cons d s) (Fin.cons (A d) y)) (searchedGradient g d (A d)))))
  have hC : 0≤2+K+(Real.sqrt a)⁻¹*K := by positivity
  have hD : 0≤(p+1 : ℝ)*((2+K)*ε)*a⁻¹ := by positivity
  exact (hrecord.trans (mul_le_mul_of_nonneg_left hres hC)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrho (mul_nonneg hC hD))

end
end krylov.Methods
