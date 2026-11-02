import krylov.Convergence.ObservableEnergy
import krylov.Convergence.ObservableSegments
import krylov.Correction.GatedNearModel
import krylov.Correction.RecordedAngle

/-!
Article: main_krylov, apG:Dunif, accepted and failed observable RFC steps.
Use: close the real model-energy/value acceptance and the dimension-sharp
projected-residual recurrence without a minimum line length or (N).
Source: true norm geometry, actual symmetric model solve and the already
proved normalized RFC projected estimates.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions krylov.Nonlinear krylov.Correction krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

omit [InnerProductSpace ℝ E] in
/-- Every energy-admitted correction leaves a nonzero real total step
and is at most half its length. Article: main_krylov, apG:Dunif. -/
theorem observable_rfc_accepted_length (line u : E) (bar : ℝ)
    (_hb : 0≤bar) (hbmax : bar≤1/16) (hline : line≠0)
    (hu : ‖u‖≤(3/2:ℝ)*bar*‖line‖) :
    line+u≠0 ∧ ‖u‖≤(1/2:ℝ)*‖line+u‖ := by
  have hfrac : ‖u‖≤(3/32:ℝ)*‖line‖ := hu.trans
    (by nlinarith only [mul_le_mul_of_nonneg_right hbmax (norm_nonneg line)])
  have hn := norm_sub_le (line+u) u
  rw [add_sub_cancel_right] at hn
  have hrel : ‖u‖≤(1/2:ℝ)*‖line+u‖ := by
    nlinarith only [hn,hfrac,norm_nonneg (line+u)]
  refine ⟨?_,hrel⟩
  intro hz
  rw [hz,norm_zero,zero_add] at hn
  have hp := norm_pos_iff.mpr hline
  nlinarith only [hn,hfrac,hp]

/-- A true line-plus-correction observation has relative secant error
at most twice the actual operator error after an energy-admitted step.
Article: main_krylov, apG:Dunif, stored-pair induction. -/
theorem observable_rfc_recorded_error (A B : E →L[ℝ] E) (line u : E) {epsilon : ℝ}
    (he : 0≤epsilon) (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤epsilon)
    (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤epsilon)
    (hu : ‖u‖≤(1/2:ℝ)*‖line+u‖) :
    ‖A line+B u-(line+u)‖≤(2*epsilon)*‖line+u‖ := by
  have ha := ((A-ContinuousLinearMap.id ℝ E).le_opNorm line).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg line))
  have hb := ((B-ContinuousLinearMap.id ℝ E).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg u))
  have hn := norm_sub_le (line+u) u
  rw [add_sub_cancel_right] at hn
  have hsum : ‖line‖+‖u‖≤2*‖line+u‖ := by linarith only [hn,hu]
  have heq : A line+B u-(line+u)=(A-ContinuousLinearMap.id ℝ E) line+
      (B-ContinuousLinearMap.id ℝ E) u := by simp only [_root_.sub_apply,ContinuousLinearMap.id_apply];module
  rw [heq]
  calc
    _ ≤ epsilon*‖line‖+epsilon*‖u‖ := (norm_add_le _ _).trans (add_le_add ha hb)
    _ = epsilon*(‖line‖+‖u‖) := by ring
    _ ≤ epsilon*(2*‖line+u‖) := mul_le_mul_of_nonneg_left hsum he
    _ = _ := by ring

omit [InnerProductSpace ℝ E] in
/-- A failed real energy gate, the true model-solve bound and a small
local operator allowance force the actual line step to be short.
Article: main_krylov, apG:Dunif, failed-gate reduction. -/
theorem observable_rfc_failed_short (u : E) (R t epsilon bar : ℝ) (N : ℕ)
    (hb : 0<bar) (ht : 0≤t)
    (hlarge : (bar/2)*t<‖u‖)
    (hu : ‖u‖≤4*(R+Real.sqrt N*((3*epsilon)*t)))
    (hsmall : 12*Real.sqrt N*epsilon≤bar/4) : t≤16*R/bar := by
  have hh := mul_le_mul_of_nonneg_right hsmall ht
  apply (le_div_iff₀ hb).mpr
  nlinarith only [hlarge,hu,hh]

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- The actual scalar value gate passes whenever the true source
segment and the derived model-energy bounds hold. Thus value acceptance
is a theorem of the observed source phase. Article: apG:Dunif. -/
theorem ObservableLocalSource.rfc_value_accept {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (a u : E) (R energy : ℝ) (ha : ‖a‖≤R) (hb : ‖a+u‖≤R) (hR : R<r)
    (hsmall : (L:ℝ)*R≤1/8)
    (hslope : inner ℝ (coordinateGradient T G a) u= -energy)
    (hu : ‖u‖^2≤(5/3:ℝ)*energy) :
    coordinateObjective T f (a+u)≤coordinateObjective T f a := by
  have hh := S.segment_value_upper a (a+u) R ha hb hR
  rw [add_sub_cancel_left,hslope] at hh
  have hcoef : (1+(L:ℝ)*R)/2≤(9/16:ℝ) := by linarith only [hsmall]
  have hquad := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖u‖)
  nlinarith only [hh,hquad,hu]

omit [CompleteSpace E] in
/-- The original genuine RFC projected-residual estimate has the
uniform n^(3/2) cubic forcing with an absolute constant. No actual line
length is bounded below. Article: main_krylov, apG:Dunif. -/
theorem observable_rfc_projected_step (s y : Fin p → E) (hs : ∀ i,s i≠0)
    (A B : E →L[ℝ] E) (g d : E) (N : ℕ) (epsilon e : ℝ)
    (hsize : p+1≤N) (he : 0≤epsilon) (he₀ : 0≤e)
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤epsilon)
    (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤epsilon)
    (hy : ∀ i,‖y i-s i‖≤(2*epsilon)*‖s i‖)
    (ho : ∀ i,inner ℝ (y i) d=0) (hc : inner ℝ d (A d)≠0)
    (hG : ‖crossGram (unitWindow (Fin.cons d s)) (unitWindow (Fin.cons d s))-1‖≤1/4)
    (hsmall : (N:ℝ)*epsilon≤1/128)
    (ht : ‖lineLength g d (A d) • d‖≤4*e)
    (hu : ‖combine (Fin.cons d s)
      (modelCoefficients (Fin.cons d s) (pairModel (Fin.cons d s) (Fin.cons (A d) y))
        (searchedGradient g d (A d)))‖≤(3/2:ℝ)*(1/16)*‖lineLength g d (A d) • d‖)
    (hline : lineLength g d (A d) • d≠0) :
    let u := combine (Fin.cons d s)
      (modelCoefficients (Fin.cons d s) (pairModel (Fin.cons d s) (Fin.cons (A d) y))
        (searchedGradient g d (A d)))
    ‖projectedResidual (unitWindow (Fin.cons (lineLength g d (A d) • d+u) s))
      (searchedGradient g d (A d)+B u)‖≤
        64*(N:ℝ)*epsilon*‖projectedResidual (unitWindow s) g‖+
          1024*(N:ℝ)*Real.sqrt N*epsilon^2*e := by
  let u := combine (Fin.cons d s)
    (modelCoefficients (Fin.cons d s) (pairModel (Fin.cons d s) (Fin.cons (A d) y))
      (searchedGradient g d (A d)))
  let line := lineLength g d (A d) • d
  have hlength := observable_rfc_accepted_length line u (1/16) (by norm_num) le_rfl hline hu
  have hdim : ((p+1:ℕ):ℝ)≤N := by exact_mod_cast hsize
  norm_num only [Nat.cast_add,Nat.cast_one] at hdim
  have hnear : (1/4:ℝ)+((p+1:ℕ):ℝ)*((1+1)*epsilon)≤1/2 := by
    norm_num only [Nat.cast_add,Nat.cast_one]
    have hh := mul_le_mul_of_nonneg_right hdim he
    nlinarith only [hh,hsmall]
  have hrelative : ‖u‖≤(1:ℝ)*‖line+u‖ := by
    rw [one_mul]
    exact hlength.2.trans (by nlinarith only [norm_nonneg (line+u)])
  have hh := near_identity_RFC_projected_estimates s y hs A B g d he (by norm_num : (0:ℝ)≤1)
    hA hB (by simpa only [show (1+1:ℝ)=2 by norm_num] using hy) ho hc hG hnear hlength.1 hrelative
  have hsqrt : (Real.sqrt (1/2:ℝ))⁻¹≤2 := by
    have hs : (1/2:ℝ)≤Real.sqrt (1/2) := Real.le_sqrt_of_sq_le (by norm_num)
    have ht := inv_anti₀ (by norm_num : (0:ℝ)<1/2) hs
    exact ht.trans_eq (by norm_num)
  have hcoef : (2+1+(Real.sqrt (1/2))⁻¹*1)*((p+1)*((2+1)*epsilon)*2)≤64*(N:ℝ)*epsilon := by
    have hh := mul_le_mul_of_nonneg_right hdim he
    have hb := mul_le_mul_of_nonneg_right (show 2+1+(Real.sqrt (1/2))⁻¹*1≤5 by linarith only [hsqrt])
      (show 0≤(p+1)*((2+1)*epsilon)*2 by positivity)
    nlinarith only [hh,hb,mul_nonneg (Nat.cast_nonneg N) he]
  have hsum : 0≤‖projectedResidual (unitWindow s) g‖+
      Real.sqrt (p+1)*(((2+1)*epsilon)*‖line‖) := by positivity
  have hbound := hh.2.trans (mul_le_mul_of_nonneg_right hcoef hsum)
  norm_num only [Nat.cast_add,Nat.cast_one] at hbound
  change ‖projectedResidual (unitWindow (Fin.cons (line+u) s)) (searchedGradient g d (A d)+B u)‖≤
    64*(N:ℝ)*epsilon*(‖projectedResidual (unitWindow s) g‖+
      Real.sqrt ((p:ℝ)+1)*(3*epsilon*‖line‖)) at hbound
  have hforcing : Real.sqrt (p+1)*(((2+1)*epsilon)*‖line‖)≤12*Real.sqrt N*epsilon*e := by
    calc
      _ ≤ Real.sqrt N*(((2+1)*epsilon)*(4*e)) := by gcongr
      _ = _ := by ring
  have hscale := mul_le_mul_of_nonneg_left hforcing (show 0≤64*(N:ℝ)*epsilon by positivity)
  norm_num only [Nat.cast_add,Nat.cast_one] at hscale
  dsimp only [line] at hscale hbound
  dsimp only
  exact hbound.trans (by nlinarith only [hscale,mul_nonneg (show 0≤(N:ℝ)*Real.sqrt N*epsilon^2 by positivity) he₀])

end
end krylov.Convergence
