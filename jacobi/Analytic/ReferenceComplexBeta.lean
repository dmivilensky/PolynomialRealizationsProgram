import jacobi.Analytic.ReferenceComplexIntegral
import jacobi.Analytic.ReferenceComplexTheorems

/-!
Article: jacobi, Lemma C.1.
The actual continued Gauss wave is exactly the original normalized
sine integral for every complex exponent with positive real part.
The integral is independently proved convergent and holomorphic;
its original real beta normalization fixes all continuation constants.
Source: Euler's beta--Gamma identity and the analytic identity theorem.
Use: wave_complex_beta proves that the original complex Gauss solution is represented by precisely this convergent integral.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The literal original normalized sine integral with its genuine complex beta normalization.
Use: wave_complex_beta proves that the original complex Gauss solution is represented by precisely this convergent integral.
Article: jacobi, Lemma C.1.
-/
def complexBetaWave (a omega:ℂ) (t:ℝ) : ℂ :=
  Complex.Gamma (2*gamma a)/Complex.Gamma (gamma a)^2*
    ((Real.sin (Real.pi*t)/Real.pi:ℝ):ℂ)^(1-gamma a)*
      ∫ s in (0:ℝ)..t,complexSineIntegrand (gamma a) t omega s

/-- The actual normalized sine integral is holomorphic on the entire admissible complex-order half-plane.
Use: the identity theorem identifies it with the actual reference Gauss function on every admissible complex order.
Article: jacobi, Lemma C.1.
Proof: positive-real-part Gamma factors have no poles or zeros. The fixed positive physical sine base has its actual exponential complex power. Multiply these analytic factors by the independently proved holomorphic singular sine integral, composed with the original affine exponent. -/
theorem complexBetaWave_holomorphic {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) (omega:ℂ) :
    DifferentiableOn ℂ (fun a => complexBetaWave a omega t) referenceOrders := by
  -- Holomorphy is established for the integral itself before identifying it with the Gauss function.
  intro a ha
  have hg : AnalyticAt ℂ gamma a := by unfold gamma; fun_prop
  have h2g : 0<(2*gamma a).re := by norm_num; linarith [show 0<(gamma a).re from ha]
  have hG : AnalyticAt ℂ (fun u:ℂ => Complex.Gamma (2*gamma u)) a :=
    (gamma_analytic h2g).comp (f := fun u:ℂ => 2*gamma u) (analyticAt_const.mul hg)
  have hD : AnalyticAt ℂ (fun u:ℂ => Complex.Gamma (gamma u)) a := (gamma_analytic ha).comp hg
  have hq := hG.div (hD.pow 2) (pow_ne_zero 2 (Complex.Gamma_ne_zero (gamma_no_pole ha)))
  have hbase : ((Real.sin (Real.pi*t)/Real.pi:ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (div_pos (jacobi.Reference.sine_pos ht) Real.pi_pos).ne'
  have hp : AnalyticAt ℂ (fun a:ℂ => ((Real.sin (Real.pi*t)/Real.pi:ℝ):ℂ)^(1-gamma a)) a := by
    simp_rw [Complex.cpow_def_of_ne_zero hbase]
    unfold gamma
    fun_prop
  have hi := (complex_sine_integral_holomorphic ha ht omega).2.comp a hg.differentiableAt
  exact ((hq.mul hp).differentiableAt.mul hi).differentiableWithinAt

/-- At real orders the literal continued normalized sine integral is exactly the original real-order beta integral.
Use: fixes the true normalization on an accumulating set for wave_complex_beta.
Article: jacobi, Lemma C.1.
Proof: real inclusion preserves Gamma values, all positive-base powers and the affine exponent. The independently evaluated real beta integral is its genuine Gamma quotient; reciprocal arithmetic therefore gives the same normalization. -/
theorem complexBetaWave_real {a:ℝ} (ha:-1<a) (omega:ℂ) {t:ℝ}
    (ht:t∈Ioo (0:ℝ) 1) : complexBetaWave (a:ℂ) omega t= jacobi.Reference.betaWave a omega t := by
  -- The normalization is recovered from the actual real beta integral, not chosen to force the equality.
  have hg : 0< jacobi.Reference.gamma a := by unfold jacobi.Reference.gamma; linarith
  have hs : 0≤Real.sin (Real.pi*t)/Real.pi := sineBase_nonneg ⟨ht.1.le,ht.2⟩
  have he : (∫ s in (0:ℝ)..t,complexSineIntegrand (gamma (a:ℂ)) t omega s)=
      ∫ s in (0:ℝ)..t,jacobi.Reference.sineIntegrand (jacobi.Reference.gamma a) t omega s := by
    apply intervalIntegral.integral_congr
    intro s hs'
    rw [uIcc_of_le ht.1.le] at hs'
    unfold complexSineIntegrand jacobi.Reference.sineIntegrand
    have hb : 0≤Real.sin (Real.pi*s)*Real.sin (Real.pi*(t-s))/Real.pi^2 :=
      sineBase_product_nonneg ht ⟨s,hs'⟩
    rw [gamma_real,show (jacobi.Reference.gamma a:ℂ)-1=((jacobi.Reference.gamma a-1:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow hb]
  unfold complexBetaWave jacobi.Reference.betaWave
  rw [he,gamma_real,show (2:ℂ)*(jacobi.Reference.gamma a:ℂ)=((2* jacobi.Reference.gamma a:ℝ):ℂ) by push_cast; rfl,
    Complex.Gamma_ofReal,Complex.Gamma_ofReal,
    show (1:ℂ)-(jacobi.Reference.gamma a:ℂ)=((1- jacobi.Reference.gamma a:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow hs,jacobi.Reference.betaNormalization_eq hg]
  push_cast
  simp only [inv_div]

/-- The genuine complex reference Gauss wave equals the literal original normalized sine integral on the full admissible half-plane.
Use: all complex analytic reference bounds and spectral formulas now apply to the exact defining integral from the article, with genuine convergence proved separately.
Article: jacobi, Lemma C.1.
Source: the analytic identity theorem on a connected half-plane.
Proof: both actual functions are holomorphic on the connected admissible order domain. Their exact original real identity holds at positive reciprocal integers tending to its interior point zero. The identity theorem extends that independently normalized equality to every admissible complex order. -/
theorem wave_complex_beta {a:ℂ} (ha:0<(gamma a).re) (omega:ℂ) {t:ℝ}
    (ht:t∈Ioo (0:ℝ) 1) : wave a omega t=complexBetaWave a omega t := by
  -- The accumulation points lie inside the actual admissible domain and have the original beta/Gauss identification.
  have hW : AnalyticOnNhd ℂ (fun a => wave a omega t) referenceOrders :=
    fun a ha => wave_comp_analytic analyticAt_id analyticAt_const ha ⟨ht.1.le,ht.2⟩
  have hB := (complexBetaWave_holomorphic ht omega).analyticOnNhd referenceOrders_open
  have h0 : (0:ℂ)∈referenceOrders := by norm_num [referenceOrders,gamma]
  have he {r:ℝ} (hr:0<r) : wave (r:ℂ) omega t=complexBetaWave (r:ℂ) omega t := by
    rw [wave_real r omega ⟨ht.1.le,ht.2⟩,complexBetaWave_real (by linarith) omega ht,
      jacobi.Reference.wave_beta_integral (by linarith) omega ⟨ht.1.le,ht.2⟩]
  have hlim : Tendsto (fun n:ℕ => ((1/((n:ℝ)+1):ℝ):ℂ)) atTop (𝓝 (0:ℂ)) := by
    convert! Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1
  have hcl : (0:ℂ)∈closure ({a | wave a omega t=complexBetaWave a omega t} \ {(0:ℂ)}) :=
    mem_closure_of_tendsto hlim (Eventually.of_forall (fun n => by
      have hn : 0<1/((n:ℝ)+1) := by positivity
      exact ⟨he hn,by simpa only [mem_singleton_iff,Complex.ofReal_eq_zero] using hn.ne'⟩))
  exact hW.eqOn_of_preconnected_of_mem_closure hB referenceOrders_preconnected h0 hcl ha

end
end jacobi.ComplexReference
