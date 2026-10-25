import polyak.General.IQC.PlantGap
import polyak.General.IQC.UniformEnergy
import polyak.General.IQC.ShiftSource
import polyak.General.IQC.CertificateNorm
import polyak.General.RootsOriginal
import polyak.Duality.Separation

/-! Article: Theorem one exponent, with its original quantifiers.
A single actual strict certificate gives a dimension- and potential-uniform
energy bound on the genuine causal heavy-ball execution. Its restarts give
a STRICT bound on the original from-rest worst-case rate. -/
noncomputable section
namespace polyak.General
open polyak General.IQC Growth Duality Spectral

def certificateGap {A B β t : ℝ}
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) : ℝ :=
  cert.ε/(1+(gradientGain A B β t)^2)

theorem certificateGap_pos {A B β t : ℝ}
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) : 0<certificateGap cert:=by
  unfold certificateGap
  exact div_pos cert.ε_pos (by positivity)

def executionConstant {A B β t : ℝ}
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) : ℝ :=
  aprioriConstant (certificateNormBound cert) (plantGain A B β t) (certificateGap cert)*
    freeGain A β (Real.exp t)

theorem executionConstant_pos {A B β t : ℝ}
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) : 0<executionConstant cert:=
  mul_pos (aprioriConstant_pos (certificateNormBound_nonneg cert)
    (plantGain_nonneg A B β t) (certificateGap_pos cert)) (freeGain_pos _ _ _)

theorem certificate_execution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {A B β t : ℝ} (hβ : 0≤β) (hB : B≠0)
    (hr : rootRadius A β<Real.exp t)
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) (r : Run E A B β) :
    SquareSummable (discountSequence t (fun k => r.x (k+1))) ∧
      sequenceNorm (discountSequence t (fun k => r.x (k+1)))≤
        executionConstant cert*(‖r.x 0‖+‖r.x 1‖) := by
  let _ : NormedSpace ℝ ((SequenceSpace E×SequenceSpace E) →L[ℝ] ℝ):=inferInstance
  let _ : SeminormedAddCommGroup ((SequenceSpace E×SequenceSpace E) →L[ℝ] ℝ):=inferInstance
  let F:=heavyBallFeedback (B:=B) hβ hr r.normalized
  let Bform:=halfLineCertificate (E:=E) cert
  have hnorm : ‖Bform‖≤certificateNormBound cert:=
    (halfLineCertificate_norm_le cert).trans (certificateForm_norm_le cert)
  have hneg (z : SequenceSpace E) :
      iqcValue Bform (F.plantL2 z) z≤ -certificateGap cert*‖z‖^2:=by
    apply halfLineCertificate_strict_graph A B β t hB cert
    intro k
    exact (stablePlant_gradientFilter A B β t hB (fun n => z n) k).symm
  have hpos (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1)
      (x : SequenceSpace E) :
      0≤ iqcValue Bform x (τ • F.deltaL2 x):=by
    exact halfGradientL2_homotopy r.normalized cert hτ x
  let f:=originalFreeResponse A β (Real.exp t) (r.x 0) (r.x 1)
  have hf : SquareSummable f:=originalFreeResponse_squareSummable hβ hr _ _
  have hh:=F.iqc_uniform_bound Bform hnorm (certificateGap_pos cert) hneg hpos
    (τ:=1) (by constructor <;> norm_num) f hf
  have he : discountSequence t (fun k => r.x (k+1))=F.run 1 f:=
    run_eq_feedback_execution hβ hr r
  rw [←he] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hfree:=originalFreeResponse_norm_bound hβ hr (r.x 0) (r.x 1)
  have hmul:=mul_le_mul_of_nonneg_left hfree
    (aprioriConstant_pos (certificateNormBound_nonneg cert)
      (plantGain_nonneg A B β t) (certificateGap_pos cert)).le
  simpa only [F,f,heavyBallFeedback,executionConstant,mul_assoc,add_comm] using hmul

theorem certificate_uniform_execution {A B β t : ℝ} (hβ : 0≤β) (hB : B≠0)
    (hr : rootRadius A β<Real.exp t)
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) :
    UniformExecutionBound A B β t (executionConstant cert) :=
  fun _ r => certificate_execution hβ hB hr cert r

def initialEnergyConstant {A B β t : ℝ}
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) : ℝ:=
  2*(executionConstant cert)^2

theorem initialEnergyConstant_pos {A B β t : ℝ}
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) :
    0< initialEnergyConstant cert := mul_pos (by norm_num) (sq_pos_of_pos (executionConstant_pos cert))

theorem certificate_uniform_energy {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {A B β t : ℝ}
    (hβ : 0≤β) (hB : B≠0) (hr : rootRadius A β<Real.exp t)
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) (r : Run E A B β) :
    Summable (discountedEnergy (fun k => r.x (k+1)) t) ∧
      (∑' k,discountedEnergy (fun k => r.x (k+1)) t k)≤
        initialEnergyConstant cert*(‖r.x 1‖^2+‖r.x 0‖^2) := by
  obtain ⟨hs,hn⟩:=certificate_execution hβ hB hr cert r
  refine ⟨by simpa only [SquareSummable,norm_discountSequence_sq] using hs,?_⟩
  have hh:=sq_le_sq₀ (sequenceNorm_nonneg (discountSequence t (fun k => r.x (k+1))))
    (mul_nonneg (executionConstant_pos cert).le (add_nonneg (norm_nonneg _) (norm_nonneg _))) |>.mpr hn
  rw [sequenceNorm_sq] at hh
  simp only [norm_discountSequence_sq] at hh
  have hcross:=mul_nonneg (sq_nonneg (executionConstant cert))
    (sq_nonneg (‖r.x 0‖-‖r.x 1‖))
  dsimp [initialEnergyConstant]
  nlinarith

theorem certificate_weighted_shift {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {A B β t : ℝ}
    (hβ : 0≤β) (hB : B≠0) (hr : rootRadius A β<Real.exp t)
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t)
    (r : Run E A B β) (k : ℕ) :
    ‖r.x (k+1)‖^2≤ initialEnergyConstant cert*
      (initialEnergyConstant cert*max 1 (Real.exp (-2*t))/
        (1+initialEnergyConstant cert*max 1 (Real.exp (-2*t))))^(k/2)*
      Real.exp (2*k*t)*(‖r.x 1‖^2+‖r.x 0‖^2) := by
  have hh:=certificate_uniform_energy hβ hB hr cert r
  apply weighted_shift (fun j => r.x (j+1)) (r.x 0) t
    (initialEnergyConstant_pos cert) hh.1 hh.2
  intro n
  have hs:=certificate_uniform_energy hβ hB hr cert (r.shift (n+1))
  simpa only [Run.shift,Nat.zero_add,Nat.add_zero,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hs.2

theorem one_exponent_growth {A B β t : ℝ} (hβ : 0≤β) (hB : B≠0)
    (hr : rootRadius A β<Real.exp t)
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) :
    growthRate A B β<Real.exp t :=
  strict_growth_of_execution hB (executionConstant_pos cert).le
    (certificate_uniform_execution hβ hB hr cert)

theorem one_exponent {μ L α β t : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0<α) (hβ : 0≤β)
    (hr : rootRadius (Dynamics.normalizedA μ L α β) β<Real.exp t)
    (cert : StrictCertificate (Waves.multiplierMap (Dynamics.normalizedA μ L α β)
      (Dynamics.normalizedB μ L α) β t) t) : Dynamics.rate μ L α β<Real.exp t := by
  have hB : Dynamics.normalizedB μ L α≠0:=by dsimp [Dynamics.normalizedB]; positivity
  exact (originalRate_le_growthRate hμ hL hα hβ).trans_lt
    (one_exponent_growth hβ hB hr cert)

theorem infeasible_zero_rate_lt_one {μ L α β : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1) (hquad : α*L<2*(1+β))
    (h : ¬∃ (ν : Spectrum) (C : ℝ),Waves.MixtureFeasible ν
      (Waves.multiplierMap (Dynamics.normalizedA μ L α β)
        (Dynamics.normalizedB μ L α) β 0) C 0) : Dynamics.rate μ L α β<1 := by
  obtain ⟨cert⟩:=(infeasible_iff_strictCertificate _ _).mp h
  have hB : 0<Dynamics.normalizedB μ L α:=by dsimp [Dynamics.normalizedB]; positivity
  have hc:=Dynamics.normalizedA_abs_add_B_lt hμ hα hquad
  have hr:=rootRadius_lt_one hβ hβ1 (by linarith : |Dynamics.normalizedA μ L α β|<1+β)
  simpa only [Real.exp_zero] using one_exponent hμ hL hα hβ
    (by simpa only [Real.exp_zero] using hr) cert

namespace Tuning
theorem one_exponent (q : Tuning) {t : ℝ} (hr : q.r0<Real.exp t)
    (cert : StrictCertificate (Waves.multiplierMap q.A q.B q.beta t) t) :
    q.rate<Real.exp t := by
  have hh:=General.one_exponent q.x_pos q.x_lt_y (by norm_num : (0:ℝ)<1)
    q.beta_nonneg (by simpa only [q.normalizedA_eq,Tuning.r0] using hr)
  apply hh
  simpa only [q.normalizedA_eq,q.normalizedB_eq] using cert

theorem infeasible_zero_rate_lt_one (q : Tuning)
    (h : ¬∃ (ν : Spectrum) (C : ℝ),
      Waves.MixtureFeasible ν (Waves.multiplierMap q.A q.B q.beta 0) C 0) : q.rate<1 := by
  obtain ⟨cert⟩:=(infeasible_iff_strictCertificate _ _).mp h
  simpa only [Real.exp_zero] using q.one_exponent
    (by simpa only [Real.exp_zero] using q.r0_lt_one) cert
end Tuning

end polyak.General
