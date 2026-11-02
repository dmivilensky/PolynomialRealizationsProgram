import krylov.Correction.GatedCutoffInvariant
import krylov.Correction.GatedTerminalContraction
import krylov.Correction.ObservedAugmentedGram

/-!
Article: main_krylov, thm:UCg, genuine terminal and scale-uniform restart bounds.
Use: Finish both real uniform gated-RFC terminal cases using actual observed
data and original spectral conditioning, with no smallest-step assumption.
Source: proved true observed energy and model residual identities, actual
spectral-gate domains and full genuine Euclidean Gram reconstruction.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- A genuine full last gated step after a good actual recorded prefix passes both real tests and has the refined quadratic-times-incoming-gradient plus cubic terminal remainder bound, even if its actual last line vanishes.
Use: Assemble the full original spectral-class gated-RFC cycle bounds.
Article: main_krylov, thm:UCg, actual terminal and scale-uniform restart.
Proof: The real old angles and measured-image conjugacy derive the true full augmented Gram. Common observed margins prove both actual gates pass and justify the original normalized inverse. Exact genuine model residual propagation, full Gram reconstruction and the actual old projected residual yield the stated terminal bound without a lower final line length.
-/
theorem gated_full_step_prefix_bound {p n : ℕ}
    (s y : Fin p → EuclideanSpace ℝ (Fin n)) (g d : EuclideanSpace ℝ (Fin n))
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hdim : p+1=n)
    {a C ε K γ : ℝ} (hp : 0<p) (hγ : 0≤γ) (hγ1 : γ<1) (ha : 0≤a)
    (hε : 0≤ε) (hK : 0≤K)
    (hprefix : recordedPrefixBound a C ε s g)
    (hA : ‖A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hB : ‖B-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hy : ∀ i, ‖y i-s i‖≤((1+K)*ε)*‖s i‖) (ho : ∀ i, inner ℝ (y i) d=0)
    (hc : inner ℝ d (A d)≠0)
    (hangle : (n : ℝ)*a≤(1-γ)/8) (hpair : (1+K)*ε≤a/2) :
    let P := gatedArrayPhase γ s y g d (A d) B
    P.trace≠[] ∧ ‖P.gradient‖≤4*(n : ℝ)*(2+K)*ε*
      (C*ε^2+Real.sqrt n*(((2+K)*ε)*‖lineLength g d (A d) • d‖)) := by
  subst n
  let U : Fin (p+1) → EuclideanSpace ℝ (Fin (p+1)) := Fin.cons d s
  let Z : Fin (p+1) → EuclideanSpace ℝ (Fin (p+1)) := Fin.cons (A d) y
  let χ := combine U (modelCoefficients U (pairModel U Z) (searchedGradient g d (A d)))
  let out := searchedGradient g d (A d)+B χ
  let η := (1+K)*ε
  have hη : 0≤η := by dsimp only [η]; positivity
  have hmargins := uniform_gate_margins (show 1≤p+1 by omega) le_rfl hγ hγ1 ha hη hpair hangle
  have hd : d≠0 := by intro hz; rw [hz,map_zero,inner_zero_left] at hc; exact hc rfl
  have hu (i : Fin (p+1)) : U i≠0 := Fin.cases hd hprefix.1 i
  have hG := unit_augmented_observed_gram s y d hprefix.1 hd ha (show η≤a by linarith) hy ho hprefix.2.1
  have hyU (i : Fin (p+1)) : ‖Z i-U i‖≤η*‖U i‖ := by
    refine Fin.cases ?_ (fun i => hy i) i
    have ht := ((A-ContinuousLinearMap.id ℝ _).le_opNorm d).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg d))
    simp only [_root_.sub_apply,ContinuousLinearMap.id_apply] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right (by dsimp only [η]; nlinarith : ε≤η) (norm_nonneg d))
  have hdefect : (p : ℝ)*(4*η)<1 := by
    have ht : (p : ℝ)≤((p+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ p
    exact (mul_le_mul_of_nonneg_right ht (by positivity)).trans_lt hmargins.2.2.2
  have hgate := pair_spectralGate_of_gram U Z hu hγ hη (by have h := hmargins.1; linarith) hyU hG hmargins.2.2.1
  have hacc := gatedArrayPhase_accepted s y g d (A d) B hp hγ hη hmargins.1 hu hyU hG hmargins.2.2.1 hdefect
  have hmodel := (normalized_pairModel_identity_distance U Z hu hη hyU hG).trans hmargins.2.1
  have hGhalf : ‖crossGram (unitWindow U) (unitWindow U)-1‖≤(1/2 : ℝ) := by
    apply hG.trans
    have hηdim : 0≤((p+1 : ℕ) : ℝ)*η := mul_nonneg (Nat.cast_nonneg _) hη
    have ht := hmargins.2.1
    linarith
  have hgram := near_identity_spectral_bounds _ (crossGram_isHermitian (unitWindow U)) hGhalf
  obtain ⟨hunit,hinv,_⟩ := near_identity_inverse _ hmodel
  have hN := normalized_pairModel_error_bound U Z hu B hε hη hB hyU
  have hρ := normalizedSearch_residual_bound s y hprefix.1 A g d hε hη hA hy ho hc
  have hres := normalizedCorrection_bound U (pairModel U Z) (fun i => ‖U i‖⁻¹)
    (unitWindow_diagonal_unit U hu) hunit B (searchedGradient g d (A d))
  change ‖projectedResidual (unitWindow U) out‖≤
    ‖correctionCompression (unitWindow U) B-rescaleModel (pairModel U Z) (fun i => ‖U i‖⁻¹)‖*
    ‖(rescaleModel (pairModel U Z) (fun i => ‖U i‖⁻¹))⁻¹‖*
      ‖projectedResidual (unitWindow U) (searchedGradient g d (A d))‖ at hres
  have hres' : ‖projectedResidual (unitWindow U) out‖≤((p+1 : ℕ) : ℝ)*(ε+η)*2*
      (‖projectedResidual (unitWindow s) g‖+Real.sqrt (p+1)*((ε+η)*‖lineLength g d (A d) • d‖)) := by
    apply hres.trans
    gcongr
  have hroot : (Real.sqrt (1/2 : ℝ))⁻¹≤2 := by
    have hr : (0 : ℝ)<Real.sqrt (1/2) := Real.sqrt_pos.mpr (by norm_num)
    have hl : (1/2 : ℝ)≤Real.sqrt (1/2) := Real.le_sqrt_of_sq_le (by norm_num)
    rw [← one_div]
    apply (div_le_iff₀ hr).mpr
    linarith
  have hframe := full_projectedResidual_lower (unitWindow U) (by norm_num : (0 : ℝ)<1/2)
    (fun i => (hgram i).1) out
  have hout := (hframe.trans (mul_le_mul_of_nonneg_right hroot (norm_nonneg _))).trans
    (mul_le_mul_of_nonneg_left hres' (by norm_num : (0 : ℝ)≤2))
  have hsum : ε+η=(2+K)*ε := by dsimp only [η]; ring
  rw [hsum] at hout
  dsimp only
  refine ⟨(gatedArrayPhase_trace_nonempty_iff γ s y g d (A d) B).mpr ⟨hgate,hp,?_⟩,?_⟩
  · exact (relative_pairDefect_norm_bound s y hprefix.1 hη hmargins.1 hy).trans_lt hdefect
  · rw [hacc.2]
    have hout' : ‖out‖≤(4*((p+1 : ℕ) : ℝ)*(2+K)*ε)*
        (‖projectedResidual (unitWindow s) g‖+Real.sqrt (p+1)*(((2+K)*ε)*‖lineLength g d (A d) • d‖)) :=
      hout.trans_eq (by ring)
    have hR := hprefix.2.2
    have hfinal := hout'.trans (mul_le_mul_of_nonneg_left (add_le_add hR (le_refl _))
      (by positivity : 0≤4*((p+1 : ℕ) : ℝ)*(2+K)*ε))
    norm_num only [Nat.cast_add,Nat.cast_one] at hfinal ⊢
    exact hfinal.trans_eq (by ring)

end
end krylov.Correction
