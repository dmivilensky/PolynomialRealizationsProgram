import polyak.Spectral.NormalizedCertificate

/-!
Article: Appendix A, complementary slackness for limiting dual symbols.
Use: every feasible spectrum has nonnegative charged moment against every compact-hull symbol,
and the symbol is real on physical frequencies.
Proof: both assertions are closed linear predicates; verify them on finite lags and the two minimizer limits.
-/

namespace polyak.Spectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology OnePoint

/-- Article: physical-frequency sampling is continuous. -/
@[fun_prop] theorem continuous_dualAngle {s : ℝ} (hs : 0<s) : Continuous (dualAngle s hs) := by
  unfold dualAngle
  fun_prop

/-- Article: real trace of every continuous symbol is integrable against a probability spectrum. -/
theorem integrable_dualTrace {s : ℝ} (hs : 0<s) (ν : Spectrum) (f : C(lagWindow s,ℂ)) :
    Integrable (fun c => (f (dualAngle s hs c)).re) (ν : Measure Frequency) :=
  integrable_continuous ν (Complex.continuous_re.comp (f.continuous.comp (continuous_dualAngle hs)))

/-- Article: integration of the real physical trace is linear. -/
def traceIntegralLinear {s : ℝ} (hs : 0<s) (ν : Spectrum) : C(lagWindow s,ℂ) →ₗ[ℝ] ℝ where
  toFun f := avg ν (fun c => (f (dualAngle s hs c)).re)
  map_add' f g := by
    simp only [avg,ContinuousMap.add_apply,Complex.add_re]
    exact integral_add (integrable_dualTrace hs ν f) (integrable_dualTrace hs ν g)
  map_smul' a f := by
    simp only [avg,ContinuousMap.smul_apply,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,smul_eq_mul,integral_const_mul,RingHom.id_apply]

/-- Article: probability integration has operator norm at most one on continuous traces. -/
theorem traceIntegralLinear_bound {s : ℝ} (hs : 0<s) (ν : Spectrum) (f : C(lagWindow s,ℂ)) :
    ‖traceIntegralLinear hs ν f‖ ≤ 1*‖f‖ := by
  have hb : ∀ᵐ c ∂(ν : Measure Frequency), ‖(f (dualAngle s hs c)).re‖ ≤ ‖f‖ :=
    Eventually.of_forall (fun c => by
      simpa only [Real.norm_eq_abs] using (Complex.abs_re_le_norm _).trans (f.norm_coe_le_norm (dualAngle s hs c)))
  have hh := norm_integral_le_of_norm_le_const hb
  simpa only [traceIntegralLinear,LinearMap.coe_mk,AddHom.coe_mk,avg,probReal_univ,
    mul_one,one_mul] using hh

/-- Article: the moment functional is continuous in the compact-function norm. -/
def traceIntegralCLM {s : ℝ} (hs : 0<s) (ν : Spectrum) : C(lagWindow s,ℂ) →L[ℝ] ℝ :=
  (traceIntegralLinear hs ν).mkContinuous 1 (traceIntegralLinear_bound hs ν)

/-- Article: the charged limiting moment is a continuous linear functional of dual coefficients. -/
def dualMomentCLM {s : ℝ} (hs : 0<s) (u C : ℝ) (ν : Spectrum) : DualCoefficient s →L[ℝ] ℝ :=
  (traceIntegralCLM hs ν).comp (evaluateDualCLM u)+
    C • ContinuousLinearMap.fst ℝ ℝ (C(lagWindow s,ℂ) × (C(lagWindow s,ℂ) × C(lagWindow s,ℂ)))

/-- Article: explicit charged moment. -/
theorem dualMomentCLM_apply {s : ℝ} (hs : 0<s) (u C : ℝ) (ν : Spectrum) (d : DualCoefficient s) :
    dualMomentCLM hs u C ν d=avg ν (fun c => (evaluateDual u d (dualAngle s hs c)).re)+d.1*C := by
  have htrace (f : C(lagWindow s,ℂ)) : traceIntegralCLM hs ν f=avg ν (fun c => (f (dualAngle s hs c)).re) := rfl
  rw [dualMomentCLM,add_apply,ContinuousLinearMap.comp_apply,
    smul_apply,htrace]
  change avg ν (fun c => (evaluateDual u d (dualAngle s hs c)).re)+C*d.1=_
  ring

/-- Article: the finite normalized lag at a physical frequency is exactly real. -/
theorem dualTrace_coefficient_coe {s : ℝ} (hs : 0<s) (u δ : ℝ) (hδ : |δ| ≤ 1)
    (n : ℕ) (c : Frequency) :
    evaluateDual u (coefficientFamily s δ hs hδ (n : OnePoint ℕ)) (dualAngle s hs c)=
      ((lagA u s (n+1) c-δ*lagB u (n+1) c)/Real.sinh ((n+1 : ℕ)*s) : ℝ) := by
  rw [evaluateDual_coefficient_coe]
  exact complexLag_arccos u s δ n hs c

/-- Article: the infinite-lag generator at a physical frequency is exactly the real minimizer gap. -/
theorem dualTrace_coefficient_infty {s : ℝ} (hs : 0<s) (u δ : ℝ) (hδ : |δ| ≤ 1) (c : Frequency) :
    evaluateDual u (coefficientFamily s δ hs hδ ∞) (dualAngle s hs c)=(g u c : ℂ) := by
  rw [evaluateDual_coefficient_infty]
  change complexGap u (Real.arccos c : ℂ)=(g u c : ℂ)
  rw [complexGap,← Complex.ofReal_cos,Real.cos_arccos c.property.1 c.property.2]
  unfold g
  push_cast
  ring

/-- Article: the charged average of a finite normalized lag is its actual normalized spectral slack. -/
theorem dualMoment_coefficient_coe {s : ℝ} (hs : 0<s) (u C δ : ℝ) (hδ : |δ| ≤ 1)
    (ν : Spectrum) (n : ℕ) :
    dualMomentCLM hs u C ν (coefficientFamily s δ hs hδ (n : OnePoint ℕ))=
      (meanA ν u s (n+1)-δ*meanB ν u (n+1))/Real.sinh ((n+1 : ℕ)*s)+δ*C := by
  rw [dualMomentCLM_apply]
  have hcharge : (coefficientFamily s δ hs hδ (n : OnePoint ℕ)).1=δ := rfl
  rw [hcharge]
  have he : (fun c : Frequency => (evaluateDual u (coefficientFamily s δ hs hδ (n : OnePoint ℕ))
      (dualAngle s hs c)).re)=
      fun c : Frequency => (lagA u s (n+1) c-δ*lagB u (n+1) c)/Real.sinh ((n+1 : ℕ)*s) := by
    funext c
    rw [dualTrace_coefficient_coe]
    rfl
  rw [he]
  unfold avg
  rw [integral_div,integral_sub (integrable_continuous ν (by unfold lagA lagD g chebT; fun_prop))
    ((integrable_continuous ν (by unfold lagB chebU; fun_prop)).const_mul δ),integral_const_mul]
  simp only [meanA_eq_integral,meanB_eq_integral,avg]

/-- Article: the infinite-lag charged moment is the actual minimizer slack. -/
theorem dualMoment_coefficient_infty {s : ℝ} (hs : 0<s) (u C δ : ℝ) (hδ : |δ| ≤ 1) (ν : Spectrum) :
    dualMomentCLM hs u C ν (coefficientFamily s δ hs hδ ∞)=meanG ν u+δ*C := by
  rw [dualMomentCLM_apply]
  have hcharge : (coefficientFamily s δ hs hδ ∞).1=δ := rfl
  rw [hcharge]
  have he : (fun c : Frequency => (evaluateDual u (coefficientFamily s δ hs hδ ∞)
      (dualAngle s hs c)).re)=(fun c : Frequency => g u c) := by
    funext c
    rw [dualTrace_coefficient_infty]
    rfl
  rw [he,meanG_eq_integral]

/-- Article: nonnegative charged moments on all actual compactified generators. -/
theorem generator_moment_nonneg {s u C : ℝ} {ν : Spectrum} (hs : 0<s)
    (h : FeasibleU u s ν C) {d : DualCoefficient s} (hd : d∈dualGenerators s hs) :
    0 ≤ dualMomentCLM hs u C ν d := by
  have hfamily (δ : ℝ) (hδ : |δ| ≤ 1) (hsign : δ=1 ∨ δ= -1) (l : OnePoint ℕ) :
      0 ≤ dualMomentCLM hs u C ν (coefficientFamily s δ hs hδ l) := by
    induction l using OnePoint.rec with
    | infty =>
      rw [dualMoment_coefficient_infty]
      have hC := abs_le.mp h.1
      rcases hsign with rfl | rfl <;> nlinarith [hC.1,hC.2]
    | coe n =>
      rw [dualMoment_coefficient_coe]
      have hn : 0<Real.sinh ((n+1 : ℕ)*s) :=
        Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (by omega)) hs)
      have hl := (h.2 (n+1) (by omega)).1
      have hr := (h.2 (n+1) (by omega)).2
      have he : (meanA ν u s (n+1)-δ*meanB ν u (n+1))/Real.sinh ((n+1 : ℕ)*s)+δ*C=
          (meanA ν u s (n+1)-δ*meanB ν u (n+1)+δ*C*Real.sinh ((n+1 : ℕ)*s))/Real.sinh ((n+1 : ℕ)*s) := by
        field_simp
      rw [he]
      apply div_nonneg _ hn.le
      rcases hsign with rfl | rfl <;> nlinarith
  rcases hd with ⟨l,rfl⟩ | ⟨l,rfl⟩
  · exact hfamily 1 (by norm_num) (Or.inl rfl) l
  · exact hfamily (-1) (by norm_num) (Or.inr rfl) l

/-- Article: complementary slackness inequality for every limiting dual point and every feasible measure. -/
theorem dualHull_moment_nonneg {s u C : ℝ} {ν : Spectrum} (hs : 0<s)
    (h : FeasibleU u s ν C) {d : DualCoefficient s} (hd : d∈dualHull s hs) :
    0 ≤ avg ν (fun c => (evaluateDual u d (dualAngle s hs c)).re)+d.1*C := by
  have hh := dualHull_le (-dualMomentCLM hs u C ν) 0
    (fun g hg => by simpa using neg_nonpos.mpr (generator_moment_nonneg hs h hg)) hd
  have hh' : 0 ≤ dualMomentCLM hs u C ν d := by simpa using neg_nonpos.mp hh
  rwa [dualMomentCLM_apply] at hh'

/-- Article: imaginary physical trace is a continuous real linear functional. -/
def dualImaginaryCLM {s : ℝ} (u : ℝ) (z : lagWindow s) : DualCoefficient s →L[ℝ] ℝ :=
  Complex.imCLM.comp ((ContinuousMap.evalCLM ℝ z).comp (evaluateDualCLM u))

/-- Article: every limiting symbol is real at every physical frequency. -/
theorem dualHull_trace_im_zero {s : ℝ} (hs : 0<s) (u : ℝ) {d : DualCoefficient s}
    (hd : d∈dualHull s hs) (c : Frequency) :
    (evaluateDual u d (dualAngle s hs c)).im=0 := by
  apply dualHull_eq (dualImaginaryCLM u (dualAngle s hs c)) 0 _ hd
  intro g hg
  have hfamily (δ : ℝ) (hδ : |δ| ≤ 1) (l : OnePoint ℕ) :
      dualImaginaryCLM u (dualAngle s hs c) (coefficientFamily s δ hs hδ l)=0 := by
    change (evaluateDual u (coefficientFamily s δ hs hδ l) (dualAngle s hs c)).im=0
    induction l using OnePoint.rec with
    | infty => rw [dualTrace_coefficient_infty]; rfl
    | coe n => rw [dualTrace_coefficient_coe]; rfl
  rcases hg with ⟨l,rfl⟩ | ⟨l,rfl⟩
  · exact hfamily 1 (by norm_num) l
  · exact hfamily (-1) (by norm_num) l

end
end polyak.Spectral
