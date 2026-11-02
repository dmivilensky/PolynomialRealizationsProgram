import krylov.Convergence.ObservableNormalization
import krylov.Convergence.ObservableEnergy
import krylov.Correction.ObservedGateAcceptance

/-!
Article: main_krylov, apG:Dunif, real observable RFC window domains.
Use: derive actual Gram/model conditioning, original solve domains and
defect-gate acceptance from the real normalized step angles and measured
pair errors maintained by the energy test. Source: finite Gram bounds,
true normalized latest-model error and measured-defect estimates.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions krylov.Correction krylov.LinearAlgebra krylov.XR
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The original observed RFC windows have all true inverse domains and
pass the genuine defect test throughout the energy-controlled phase.
No independence, inverse or gate decision is an additional assumption.
Article: main_krylov, apG:Dunif. -/
theorem observable_rfc_window_domains (s y : Fin p → E) (hs : ∀ i,s i≠0)
    (N : ℕ) (epsilon bar : ℝ) (hn : 1≤N) (hsize : p≤N)
    (he : 0≤epsilon) (hb : 0≤bar) (hsmall : (N:ℝ)*epsilon≤1/128)
    (hbar : (N:ℝ)*bar≤1/16)
    (hy : ∀ i,‖y i-s i‖≤(2*epsilon)*‖s i‖)
    (hangle : ∀ i j,i≠j → |inner ℝ (unitWindow s i) (unitWindow s j)|≤2*epsilon+3*bar) :
    ‖crossGram (unitWindow s) (unitWindow s)-1‖≤1/4 ∧
    ‖rescaleModel (pairModel s y) (fun i=>‖s i‖⁻¹)-1‖≤1/4 ∧
    IsUnit (crossGram y s).det ∧ IsUnit (pairModel s y).det ∧
    ‖pairDefect s y‖<1 ∧
    (∀ i,(3/4:ℝ)≤(crossGram_isHermitian (unitWindow s)).eigenvalues i) := by
  have hn' : (1:ℝ)≤N := by exact_mod_cast hn
  have hp' : (p:ℝ)≤N := by exact_mod_cast hsize
  have hpε := (mul_le_mul_of_nonneg_right hp' he).trans hsmall
  have hpbar := (mul_le_mul_of_nonneg_right hp' hb).trans hbar
  have hεN : epsilon≤(N:ℝ)*epsilon := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hn' he
  have hε : epsilon≤1/128 := hεN.trans hsmall
  have hunit := unitWindow_norm s hs
  have hη : 0≤2*epsilon := by positivity
  have hδ : 0≤2*epsilon+3*bar := by positivity
  have hgram := observable_gram_angular (unitWindow s) hunit hδ hangle
  have hmargin : (p:ℝ)*(2*epsilon+3*bar)+(p:ℝ)*(2*epsilon)≤1/4 := by
    nlinarith only [hpε,hpbar]
  have hGquarter : ‖crossGram (unitWindow s) (unitWindow s)-1‖≤1/4 :=
    hgram.trans (by nlinarith only [hmargin,mul_nonneg (Nat.cast_nonneg p) hη])
  have hmodel := (normalized_pairModel_identity_distance s y hs hη hy hgram).trans hmargin
  have hnormalizedC := observable_crossGram_domain (unitWindow s) (unitWindowImages s y)
    hunit hη hgram (unitWindow_image_error s y hs hy) hmargin
  have hC := observable_raw_unit_of_normalized s y hnormalizedC.1
  have hId (c : Fin p → ℝ) : 1*‖WithLp.toLp 2 c‖^2≤c ⬝ᵥ ((1:Matrix (Fin p) (Fin p) ℝ)*ᵥc) := by
    rw [observable_identity_form,one_mul]
  have hform (c : Fin p → ℝ) : (3/4:ℝ)*‖WithLp.toLp 2 c‖^2≤
      c ⬝ᵥ (rescaleModel (pairModel s y) (fun i=>‖s i‖⁻¹)*ᵥc) :=
    (observable_coefficient_sandwich _ hmodel c).1
  have hTnormalized := (coefficient_inverse_of_coercivity _ (3/4) (by norm_num) hform).1
  have hT : IsUnit (pairModel s y).det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply isUnit_iff_ne_zero.mp hTnormalized
    rw [rescaleModel,det_mul,det_mul,hz,mul_zero,zero_mul]
  have hdefect := relative_pairDefect_norm_bound s y hs hη (by linarith only [hε]) hy
  have hdefect1 : ‖pairDefect s y‖<1 := hdefect.trans_lt (by nlinarith only [hpε])
  have hGform (c : Fin p → ℝ) : (3/4:ℝ)*‖WithLp.toLp 2 c‖^2≤
      c ⬝ᵥ (crossGram (unitWindow s) (unitWindow s)*ᵥc) :=
    (observable_coefficient_sandwich _ hGquarter c).1
  exact ⟨hGquarter,hmodel,hC,hT,hdefect1,observable_gram_spectral _ _ hGform⟩

end
end krylov.Convergence
