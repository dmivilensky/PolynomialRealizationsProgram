import polyak.General.Regions.OneAtom
import polyak.General.Regions.QuadraticLower
import polyak.General.RootsDominant

/-! Article: Theorem B(c), strict nonlinear rate above the entire underdamped
quadratic plateau, including its two critical-damping endpoints. -/
namespace polyak.General.Regions
noncomputable section
open Dynamics Spectral Filter
open scoped Topology

private theorem single_feasible_of_negative_gap (q : Tuning) (c : Frequency) {t : ℝ}
    (_ht : t<0) (hg : 0≤1-Complex.normSq (Waves.multiplierMap q.A q.B q.beta t c))
    (hgap : 2*|(Waves.multiplierMap q.A q.B q.beta t c).im|≤
      (1-Complex.normSq (Waves.multiplierMap q.A q.B q.beta t c))*(Real.cosh t-1)) :
    Waves.MixtureFeasible (oneAtom c) (Waves.multiplierMap q.A q.B q.beta t) 0 t := by
  rw [oneAtom_feasible_iff]
  refine ⟨by simpa using hg,fun n hn=>?_⟩
  have hcosh : Real.cosh t≤Real.cosh (n*t) := by
    apply Real.cosh_le_cosh.mpr
    simp only [abs_mul,Nat.abs_cast]
    have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
    nlinarith [abs_nonneg t]
  have hb : |2*(Waves.multiplierMap q.A q.B q.beta t c).im*Real.sin (n*Real.arccos c)|≤
      2*|(Waves.multiplierMap q.A q.B q.beta t c).im| := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  have hs : (1-Complex.normSq (Waves.multiplierMap q.A q.B q.beta t c))*(Real.cosh t-1)≤
      (1-Complex.normSq (Waves.multiplierMap q.A q.B q.beta t c))*
        (Real.cosh (n*t)-Real.cos (n*Real.arccos c)) :=
    mul_le_mul_of_nonneg_left (by linarith [Real.cos_le_one (n*Real.arccos c)]) hg
  simp only [zero_mul,add_zero,sub_zero]
  constructor <;> linarith [(abs_le.mp hb).1,(abs_le.mp hb).2]

/-- Any zero multiplier at a negative exponent can be moved to a strictly larger exponent. -/
theorem rate_gt_of_zero_multiplier (q : Tuning) (c : Frequency) {t₀ : ℝ}
    (ht₀ : t₀<0) (hm : Waves.multiplierMap q.A q.B q.beta t₀ c=0) :
    Real.exp t₀<Dynamics.rate q.x q.y 1 q.beta := by
  let m := fun t : ℝ=>Waves.multiplierMap q.A q.B q.beta t c
  have hmcont : Continuous m := by
    change Continuous (fun t : ℝ=>Waves.multiplier q.A q.B q.beta t (Real.arccos c))
    unfold Waves.multiplier Waves.z
    have hB : (q.B:ℂ)≠0 := by exact_mod_cast q.B_ne_zero
    fun_prop (disch := aesop)
  have hgcont : Continuous (fun t=>1-Complex.normSq (m t)) := by fun_prop
  have hgapcont : Continuous (fun t=>(1-Complex.normSq (m t))*(Real.cosh t-1)-2*|(m t).im|) := by
    fun_prop
  have hg0 : 0<1-Complex.normSq (m t₀) := by simp only [m,hm,map_zero,sub_zero]; norm_num
  have hgap0 : 0<(1-Complex.normSq (m t₀))*(Real.cosh t₀-1)-2*|(m t₀).im| := by
    simp only [m,hm,map_zero,sub_zero,Complex.zero_im,abs_zero,mul_zero,one_mul]
    exact sub_pos.mpr (Real.one_lt_cosh.mpr (ne_of_lt ht₀))
  have hev : ∀ᶠ t in 𝓝 t₀,t<0 ∧ 0<1-Complex.normSq (m t) ∧
      0<(1-Complex.normSq (m t))*(Real.cosh t-1)-2*|(m t).im| :=
    (eventually_lt_nhds ht₀).and ((hgcont.continuousAt.eventually (eventually_gt_nhds hg0)).and
      (hgapcont.continuousAt.eventually (eventually_gt_nhds hgap0)))
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hev
  let t := t₀+ε/2
  have hdist : dist t t₀<ε := by dsimp [t]; rw [Real.dist_eq,add_sub_cancel_left,abs_of_pos (by positivity)]; linarith
  obtain ⟨ht,hg,hgap⟩ := hball hdist
  have hh := oneAtom_exp_le_originalRate q c
    (single_feasible_of_negative_gap q c ht hg.le (by linarith))
    (fun hpos=>False.elim (not_lt_of_ge ht.le hpos))
  exact (Real.exp_lt_exp.mpr (by dsimp [t]; linarith)).trans_le hh

/-- A literal zero multiplier at the central curvature of the underdamped plateau. -/
theorem exists_zero_multiplier_of_underdamped (q : Tuning)
    (hq : q.rhoQ=Real.sqrt q.beta) :
    0<Real.sqrt q.beta ∧ ∃ c : Frequency,
      Waves.multiplierMap q.A q.B q.beta (Real.log (Real.sqrt q.beta)) c=0 := by
  have hrpos : 0<Real.sqrt q.beta := by
    rw [← hq,← q.quadraticRate_eq]
    exact Growth.quadraticRate_pos q.x_pos q.x_lt_y (by norm_num) q.beta_nonneg q.beta_lt_one
      (by simpa using q.y_lt)
  have hd := q.damping_iff.mp hq
  have hs := Real.sq_sqrt q.beta_nonneg
  have hA : -2*Real.sqrt q.beta<q.A ∧ q.A<2*Real.sqrt q.beta := by
    dsimp [Tuning.A]
    constructor <;> nlinarith [q.x_lt_y,hd.1,hd.2]
  let c : Frequency := ⟨q.A/(2*Real.sqrt q.beta),by
    constructor
    · exact (le_div_iff₀ (by positivity)).mpr (by linarith [hA.1])
    · exact (div_le_one (by positivity)).mpr hA.2.le⟩
  let t := Real.log (Real.sqrt q.beta)
  let z := Waves.z t (Real.arccos c)
  have hz : z≠0 := Waves.z_ne_zero _ _
  have hre : z.re=Real.sqrt q.beta*(c:ℝ) := by
    have hh := Waves.z_pow_re t (Real.arccos c) 1
    simpa only [pow_one,Nat.cast_one,one_mul,t,Real.exp_log hrpos,
      Real.cos_arccos c.property.1 c.property.2] using hh
  have hnorm : Complex.normSq z=q.beta := by
    rw [Complex.normSq_eq_norm_sq]
    have hh := Waves.norm_z_pow t (Real.arccos c) 1
    simp only [pow_one,Nat.cast_one,one_mul,t,Real.exp_log hrpos] at hh
    change ‖z‖=Real.sqrt q.beta at hh
    rw [hh,hs]
  have hdiv : (q.beta:ℂ)/z=starRingEnd ℂ z := by
    apply (div_eq_iff hz).mpr
    have hh := hnorm
    rw [Complex.normSq_apply] at hh
    apply Complex.ext <;> simp only [Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,
      Complex.conj_re,Complex.conj_im]
    · nlinarith
    · ring
  refine ⟨hrpos,c,?_⟩
  change (z+(q.beta:ℂ)/z-(q.A:ℂ))/(q.B:ℂ)=0
  rw [hdiv]
  have he : z+starRingEnd ℂ z-(q.A:ℂ)=0 := by
    apply Complex.ext
    · simp only [Complex.add_re,Complex.sub_re,Complex.conj_re,Complex.ofReal_re,Complex.zero_re]
      rw [hre]
      dsimp [c]
      field_simp
      ring
    · simp
  rw [he,zero_div]

/-- Theorem B(c), strict actual nonlinear gap even at critical damping. -/
theorem underdamped_rate_strict (q : Tuning) (hq : q.rhoQ=Real.sqrt q.beta) :
    q.rhoQ<Dynamics.rate q.x q.y 1 q.beta := by
  obtain ⟨hr,c,hm⟩ := exists_zero_multiplier_of_underdamped q hq
  have hr1 : Real.sqrt q.beta<1 := by simpa using Real.sqrt_lt_sqrt q.beta_nonneg q.beta_lt_one
  have hh := rate_gt_of_zero_multiplier q c (Real.log_neg hr hr1) hm
  simpa only [hq,Real.exp_log hr] using hh

end
end polyak.General.Regions
