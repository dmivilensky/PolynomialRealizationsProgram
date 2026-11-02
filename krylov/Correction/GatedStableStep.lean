import krylov.Correction.GatedNearModel
import krylov.Correction.RecordedAngle

/-!
Article: main_krylov, thm:UCq and thm:UCg, genuine uniform finite-cycle step.
Use: Close the actual Gram, angle, gate and projected-residual induction
before the first small line displacement, using one fixed quantitative allowance.
Source: proved real observed conjugacy and spectral gates, true normalized
model solves, actual recorded-step transfer and elementary scalar inequalities.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ}

/-- The real spectral-gated RFC step has accepted tests, a nonzero recorded movement, controlled true new/old angles and the original quantitative recorded-residual bound under the genuine large-line conditions.
Use: Assemble the actual uniform gated-RFC cutoff induction from original measured data.
Article: main_krylov, thm:UCq and thm:UCg, genuine finite-cycle cutoff step.
Proof: True pair and augmented-Gram margins derive both real accepted branches. The actual normalized model inverse bounds the real correction by its searched residual; the genuine line/residual ratio makes it strictly smaller than the true line displacement. Proved noncancellation and actual normalization give all new/old angles. The original projected-residual theorem then propagates the real next recorded-window residual using the already derived actual relative-correction bound.
-/
theorem gated_stable_recorded_step (s y : Fin p → E) (hs : ∀ i, s i≠0)
    (A B : E →L[ℝ] E) (g d : E) {N : ℕ} {ε K γ δ q : ℝ}
    (hp : 0<p) (hsize : p+1≤N) (hε : 0≤ε) (hK : 0≤K) (hγ : 0≤γ) (hq : q<1)
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤ε) (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ε)
    (hy : ∀ i, ‖y i-s i‖≤((1+K)*ε)*‖s i‖) (ho : ∀ i, inner ℝ (y i) d=0)
    (hc : inner ℝ d (A d)≠0)
    (hG : ‖crossGram (unitWindow (Fin.cons d s)) (unitWindow (Fin.cons d s))-1‖≤δ)
    (hhalf : (1+K)*ε≤1/2) (hnear : δ+((p+1 : ℕ) : ℝ)*((1+K)*ε)≤1/2)
    (hmargin : δ+((p+1 : ℕ) : ℝ)*((1+K)*ε)+γ*((1+K)*ε)≤1-γ)
    (hdefect : (p : ℝ)*(4*((1+K)*ε))<1)
    (hline : 0<‖lineLength g d (A d) • d‖)
    (hcut : 4*(‖projectedResidual (unitWindow s) g‖+
      Real.sqrt N*(((2+K)*ε)*‖lineLength g d (A d) • d‖))≤q*‖lineLength g d (A d) • d‖)
    (hrelative : ‖(gatedArrayPhase γ s y g d (A d) B).movement‖≤K*
      ‖lineLength g d (A d) • d+(gatedArrayPhase γ s y g d (A d) B).movement‖) :
    let P := gatedArrayPhase γ s y g d (A d) B
    let line := lineLength g d (A d) • d
    let step := line+P.movement
    ‖P.movement‖≤q*‖line‖ ∧ step≠0 ∧
      (∀ i, |inner ℝ (unitWindow s i) (NormedSpace.normalize step)|≤(1+K)*ε+2*q) ∧
      ‖projectedResidual (unitWindow (Fin.cons step s)) P.gradient‖≤
        ((2+K+(Real.sqrt (1/2))⁻¹*K)*((p+1)*((2+K)*ε)*2))*
          (‖projectedResidual (unitWindow s) g‖+
            Real.sqrt (p+1)*(((2+K)*ε)*‖line‖)) := by
  let U : Fin (p+1) → E := Fin.cons d s
  let Z : Fin (p+1) → E := Fin.cons (A d) y
  let χ := combine U (modelCoefficients U (pairModel U Z) (searchedGradient g d (A d)))
  let line := lineLength g d (A d) • d
  have hη : 0≤(1+K)*ε := by positivity
  have hd : d≠0 := by intro hz; rw [hz,map_zero,inner_zero_left] at hc; exact hc rfl
  have hu (i : Fin (p+1)) : U i≠0 := Fin.cases hd hs i
  have hyU (i : Fin (p+1)) : ‖Z i-U i‖≤((1+K)*ε)*‖U i‖ := by
    refine Fin.cases ?_ (fun i => hy i) i
    have he := ((A-ContinuousLinearMap.id ℝ E).le_opNorm d).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg d))
    simp only [_root_.sub_apply,ContinuousLinearMap.id_apply] at he
    exact he.trans (mul_le_mul_of_nonneg_right (by nlinarith : ε≤(1+K)*ε) (norm_nonneg d))
  have hacc := gatedArrayPhase_accepted s y g d (A d) B hp hγ hη hhalf hu hyU hG hmargin hdefect
  have hmove : (gatedArrayPhase γ s y g d (A d) B).movement=χ := hacc.1
  have hgrad : (gatedArrayPhase γ s y g d (A d) B).gradient=searchedGradient g d (A d)+B χ := hacc.2
  have hδhalf : δ≤1/2 := by nlinarith [mul_nonneg (Nat.cast_nonneg (p+1)) hη]
  have hmodel := (normalized_pairModel_identity_distance U Z hu hη hyU hG).trans hnear
  have hm := near_identity_model_movement U Z hu (searchedGradient g d (A d)) hmodel (hG.trans hδhalf)
  have hsearch := normalizedSearch_residual_bound s y hs A g d hε hη hA hy ho hc
  rw [show ε+(1+K)*ε=(2+K)*ε by ring] at hsearch
  have hχq : ‖χ‖≤q*‖line‖ := by
    apply (hm.trans (mul_le_mul_of_nonneg_left hsearch (by norm_num : (0 : ℝ)≤4))).trans
    apply LE.le.trans ?_ hcut
    gcongr
    exact_mod_cast hsize
  have hv := recorded_step_nonzero line χ hline hq hχq
  have hrel : ‖χ‖≤K*‖line+χ‖ := by simpa only [hmove] using hrelative
  have hres := near_identity_RFC_projected_estimates s y hs A B g d hε hK hA hB hy ho hc hG hnear hv hrel
  dsimp only
  rw [hmove,hgrad]
  refine ⟨hχq,hv,?_,hres.2⟩
  intro i
  have horth : inner ℝ (rescaleWindow y (fun j => ‖s j‖⁻¹) i) line=0 := by
    simp only [rescaleWindow,line,real_inner_smul_left,real_inner_smul_right,ho,mul_zero]
  exact recorded_step_observed_angle (unitWindow s i) (rescaleWindow y (fun j => ‖s j‖⁻¹) i)
    line χ (unitWindow_norm s hs i) (unitWindow_pair_error s y hs hy i) horth hline hq hχq

end
end krylov.Correction
