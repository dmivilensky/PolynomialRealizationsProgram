import krylov.Correction.GatedAccepted
import krylov.Methods.ProjectedResidual

/-!
Article: main_krylov, thm:UCq and thm:UCg, actual near-identity residual step.
Use: Derive true correction and recorded-residual estimates from genuine
Gram/pair bounds, with every normalized inverse domain proved first.
Source: existing normalized RFC projected-residual theorem, actual observed
model/Gram comparison and genuine near-identity spectral inverse bounds.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ}

/-- A genuine near-identity normalized model and Gram bound control the actual physical model correction by four times its real projected incoming gradient.
Use: Propagate the true projected residual in the uniform RFC finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, actual near-identity residual step.
Proof: The true normalized matrix inverse has norm at most two, and actual physical synthesis has bound two. Apply the original exact normalized movement theorem after deriving both bounds.
-/
theorem near_identity_model_movement (s y : Fin p → E) (hs : ∀ i, s i≠0) (g : E)
    (hmodel : ‖rescaleModel (pairModel s y) (fun i => ‖s i‖⁻¹)-1‖≤(1/2 : ℝ))
    (hgram : ‖crossGram (unitWindow s) (unitWindow s)-1‖≤(1/2 : ℝ)) :
    ‖combine s (modelCoefficients s (pairModel s y) g)‖≤4*‖projectedResidual (unitWindow s) g‖ := by
  have hinv := (near_identity_inverse _ hmodel).2.1
  have hm := normalizedCorrection_movement_bound s (pairModel s y) (fun i => ‖s i‖⁻¹)
    (unitWindow_diagonal_unit s hs) g (by norm_num : (0 : ℝ)≤4) (gram_near_norm_le _ hgram)
  change ‖combine s (modelCoefficients s (pairModel s y) g)‖≤
    Real.sqrt 4*‖(rescaleModel (pairModel s y) (fun i => ‖s i‖⁻¹))⁻¹‖*‖projectedResidual (unitWindow s) g‖ at hm
  have ht := hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinv (Real.sqrt_nonneg 4)) (norm_nonneg _))
  simpa only [show Real.sqrt (4 : ℝ)=2 by norm_num,show (2 : ℝ)*2=4 by norm_num] using ht

/-- The original RFC solve has uniform correction and true recorded-residual bounds from actual relative secant errors and a genuine near-identity augmented Gram.
Use: Propagate the true projected residual in the uniform RFC finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, actual near-identity residual step.
Proof: The true nonzero current curvature and actual old columns justify normalization. Relative observed errors give the genuine normalized model distance to the identity; the real spectral bounds derive every inverse and Gram domain. Reuse the complete original normalized projected-residual theorem and its real search residual bound.
-/
theorem near_identity_RFC_projected_estimates (s y : Fin p → E) (hs : ∀ i, s i≠0)
    (A B : E →L[ℝ] E) (g d : E) {ε K δ : ℝ} (hε : 0≤ε) (hK : 0≤K)
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤ε) (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ε)
    (hy : ∀ i, ‖y i-s i‖≤((1+K)*ε)*‖s i‖) (ho : ∀ i, inner ℝ (y i) d=0)
    (hc : inner ℝ d (A d)≠0)
    (hG : ‖crossGram (unitWindow (Fin.cons d s)) (unitWindow (Fin.cons d s))-1‖≤δ)
    (hnear : δ+((p+1 : ℕ) : ℝ)*((1+K)*ε)≤1/2)
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
    let R := ‖projectedResidual (unitWindow s) g‖
    let t := ‖lineLength g d (A d) • d‖
    let χ := combine U (modelCoefficients U H (searchedGradient g d (A d)))
    ‖χ‖≤4*(R+Real.sqrt (p+1)*(((2+K)*ε)*t)) ∧
      ‖projectedResidual (unitWindow (Fin.cons (lineLength g d (A d) • d+χ) s))
        (searchedGradient g d (A d)+B χ)‖≤
          ((2+K+(Real.sqrt (1/2))⁻¹*K)*((p+1)*((2+K)*ε)*2))*
            (R+Real.sqrt (p+1)*(((2+K)*ε)*t)) := by
  have hη : 0≤(1+K)*ε := by positivity
  have hd : d≠0 := by intro hz; rw [hz,map_zero,inner_zero_left] at hc; exact hc rfl
  have hu (i : Fin (p+1)) : (Fin.cons d s : Fin (p+1) → E) i≠0 := Fin.cases hd hs i
  have hyU (i : Fin (p+1)) : ‖(Fin.cons (A d) y : Fin (p+1) → E) i-
      (Fin.cons d s : Fin (p+1) → E) i‖≤((1+K)*ε)*‖(Fin.cons d s : Fin (p+1) → E) i‖ := by
    refine Fin.cases ?_ (fun i => hy i) i
    have he := ((A-ContinuousLinearMap.id ℝ E).le_opNorm d).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg d))
    simp only [_root_.sub_apply,ContinuousLinearMap.id_apply] at he
    simpa only [Fin.cons_zero] using he.trans (mul_le_mul_of_nonneg_right (by nlinarith : ε≤(1+K)*ε) (norm_nonneg d))
  have hmodel := near_identity_spectral_bounds _ (rescale_pairModel_isHermitian (Fin.cons d s) (Fin.cons (A d) y) _)
    ((normalized_pairModel_identity_distance _ _ hu hη hyU hG).trans hnear)
  have hδhalf : δ≤1/2 := by nlinarith [mul_nonneg (Nat.cast_nonneg (p+1)) hη]
  have hgram := near_identity_spectral_bounds _ (crossGram_isHermitian (unitWindow (Fin.cons d s))) (hG.trans hδhalf)
  have h := normalizedRFC_projected_estimates s y hs A B g d
    (by norm_num : (0 : ℝ)<1/2) (by norm_num : (0 : ℝ)≤4) hε hK hA hB hy ho hc
    (fun i => (hmodel i).1) (fun i => ⟨by have hi := (hgram i).1; linarith,(hgram i).2⟩) hv hχ
  refine ⟨?_,?_⟩
  · have ht := h.2.2.1.trans (mul_le_mul_of_nonneg_left h.2.1 (by positivity))
    simpa only [show Real.sqrt (4 : ℝ)=2 by norm_num,show (1/2 : ℝ)⁻¹=2 by norm_num,mul_assoc,
      show (2 : ℝ)*2=4 by norm_num] using ht
  · simpa only [show (1/2 : ℝ)⁻¹=2 by norm_num] using h.2.2.2

end
end krylov.Correction
