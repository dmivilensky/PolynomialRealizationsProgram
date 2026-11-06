import nesterov.Faithful.Low
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Big-O expansions and the principal low-frequency phase lead. -/
namespace nesterov.Faithful
noncomputable section
open Filter Asymptotics Polynomial
open scoped Topology

theorem product_isBigO (u q : Polynomial ℝ) {y : ℝ} (hy : 0<y)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) :
    (fun ω : ℝ=>limitProduct u q ω-(-(ω:ℂ)^2/y+Complex.I*(effectiveLead u q y/y:ℝ)*(ω:ℂ)^3))
      =O[𝓝 (0:ℝ)] (fun ω : ℝ=>(ω:ℂ)^4) := by
  obtain ⟨R,hR,he⟩ := product_expansion u q hy hu hq
  have hh := (isBigO_refl (fun ω : ℝ=>(ω:ℂ)^4) (𝓝 (0:ℝ))).mul (hR.continuousAt.isBigO (F:=ℂ))
  simp only [mul_one] at hh
  exact hh.congr_left (fun ω=>by rw [he];ring)

theorem symbol_isBigO (u q : Polynomial ℝ) {y : ℝ} (hy : 0<y)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) :
    (fun ω : ℝ=>limitSymbol u q ω-((2*effectiveLead u q y-1)/(2*y))*ω^4)
      =O[𝓝 (0:ℝ)] (fun ω : ℝ=>ω^6) := by
  obtain ⟨R,hR,he⟩ := symbol_expansion u q hy hu hq
  have hh := (isBigO_refl (fun ω : ℝ=>ω^6) (𝓝 (0:ℝ))).mul (hR.continuousAt.isBigO (F:=ℝ))
  simp only [mul_one] at hh
  exact hh.congr_left (fun ω=>by rw [he];ring)

def limitAngle (u q : Polynomial ℝ) (ω : ℝ) : ℝ := (-star (limitProduct u q ω)).arg

theorem phase_lead_limit (u q : Polynomial ℝ) {y : ℝ} (hy : 0<y)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) :
    Tendsto (fun ω : ℝ=>limitAngle u q ω/ω) (𝓝[≠] (0:ℝ)) (𝓝 (effectiveLead u q y)) := by
  obtain ⟨X,_,hX0,hXd,hprod⟩ := exists_product_germ u q hy hu hq
  let f : ℝ→ℂ := fun ω=> -star (X ω)
  have hf0 : f 0=((1/y:ℝ):ℂ) := by simp [f,hX0,neg_div]
  have hfd : HasDerivAt f (Complex.I*(effectiveLead u q y/y:ℝ)) 0 := by
    convert! hXd.star.neg using 1
    simp only [star_mul,star_div₀,Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
    push_cast
    ring
  have hz : f 0∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by
    rw [hf0,Complex.ofReal_re]
    exact one_div_pos.mpr hy))
  have hlog : HasDerivAt (fun ω=>Complex.log (f ω)) (Complex.I*(effectiveLead u q y:ℝ)) 0 := by
    have hh := ((Complex.hasDerivAt_log hz).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hfd
    convert! hh using 1
    change Complex.I*(effectiveLead u q y:ℝ)=
      (Complex.I*(effectiveLead u q y/y:ℝ))*(f 0)⁻¹
    rw [hf0]
    push_cast
    field_simp [hy.ne']
  have hArg : HasDerivAt (fun ω=>Complex.arg (f ω)) (effectiveLead u q y) 0 := by
    simpa [Function.comp_def,Complex.log_im] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hlog
  have hArg0 : Complex.arg (f 0)=0 := by
    rw [hf0]
    exact Complex.arg_ofReal_of_nonneg (one_div_pos.mpr hy).le
  have ht := hArg.tendsto_slope_zero
  simp only [zero_add,hArg0,sub_zero,smul_eq_mul,←div_eq_inv_mul] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ω hω
  have hn : ω≠0 := hω
  have he : -star (limitProduct u q ω)=(ω^2:ℝ)*f ω := by
    rw [hprod]
    simp only [star_mul,star_pow,Complex.star_def,Complex.conj_ofReal,f]
    push_cast
    ring
  rw [limitAngle,he,Complex.arg_real_mul _ (sq_pos_of_ne_zero hn)]

end
end nesterov.Faithful
