import nesterov.Faithful.Degenerate
import nesterov.Faithful.TraceLimit

/-! Existence and the order of the article's first nonzero even symbol term. -/
namespace nesterov.Faithful
noncomputable section
open Filter Set Polynomial Asymptotics
open scoped Topology

theorem analyticAt_limitSymbol (u q : Polynomial ℝ) (ω : ℝ) :
    AnalyticAt ℝ (limitSymbol u q) ω := by
  have hc := analyticAt_circle ω
  have hu := AnalyticAt.fun_comp (f:=circle) (analyticAt_evalComplex u (circle ω)) hc
  have hq := AnalyticAt.fun_comp (f:=circle) (analyticAt_evalComplex q (circle ω)) hc
  have h1 : AnalyticAt ℝ (fun _ : ℝ=>(1:ℂ)) ω := analyticAt_const
  have hv : AnalyticAt ℝ (fun x=>(circle x-1)^2*evalComplex q (circle x)) ω :=
    ((hc.sub h1).fun_pow 2).fun_mul hq
  have hp := hv.neg.fun_mul (analyticAt_star (hu.sub hv))
  exact (Complex.reCLM.analyticAt _).fun_comp ((h1.sub hc).fun_mul hp)

theorem symbol_isBigO_four (u q : Polynomial ℝ) {y : ℝ} (hy : 0<y)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) :
    limitSymbol u q=O[𝓝 (0:ℝ)] (fun ω : ℝ=>ω^4) := by
  obtain ⟨R,hR,he⟩ := symbol_expansion u q hy hu hq
  let B : ℝ→ℝ := fun ω=>(2*effectiveLead u q y-1)/(2*y)+ω^2*R ω
  have hB : AnalyticAt ℝ B 0 := analyticAt_const.add ((analyticAt_id.fun_pow 2).fun_mul hR)
  have hh := (isBigO_refl (fun ω : ℝ=>ω^4) (𝓝 (0:ℝ))).mul (hB.continuousAt.isBigO (F:=ℝ))
  exact (hh.congr_right (fun ω=>mul_one _)).congr_left (fun ω=>by rw [he];dsimp [B];ring)

theorem leading_even_order_ge_two {u q : Polynomial ℝ} {y : ℝ} (hy : 0<y)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) {p : ℕ} {s : ℝ}
    (hterm : HasLeadingEvenTerm u q p s) : 2≤p := by
  by_contra hn
  have hlt : 2*p<4 := by omega
  have hh := (symbol_isBigO_four u q hy hu hq).trans_isLittleO (isLittleO_pow_pow hlt)
  have ht := hh.tendsto_div_nhds_zero.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  exact hterm.1 (tendsto_nhds_unique (leading_even_ratio hterm) ht)

/-- A nonzero real-analytic even symbol has exactly the even leading-term
form used in the article, with an analytic O(ω^(2p+2)) remainder. -/
theorem exists_leading_even_term (u q : Polynomial ℝ) {y : ℝ} (hy : 0<y)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y)
    (hnonzero : ∃ ω : ℝ,limitSymbol u q ω≠0) :
    ∃ p : ℕ,2≤p ∧ ∃ s : ℝ,HasLeadingEvenTerm u q p s := by
  have hf := analyticAt_limitSymbol u q 0
  have hlocal : ¬∀ᶠ ω in 𝓝 (0:ℝ),limitSymbol u q ω=0 := by
    intro hh
    have ho := analyticOrderAt_eq_top.mpr hh
    have heq := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 (analyticAt_limitSymbol u q)).mp ho
    obtain ⟨ω,hω⟩ := hnonzero
    exact hω (congrFun heq ω)
  obtain ⟨n,g,hg,hg0,hfac⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hlocal
  simp only [sub_zero,smul_eq_mul] at hfac
  have htneg : Tendsto (fun ω : ℝ=> -ω) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
    simpa only [neg_zero] using continuous_neg.tendsto (0:ℝ)
  have hneg : ∀ᶠ ω in 𝓝 (0:ℝ),limitSymbol u q (-ω)=(-ω)^n*g (-ω) := by
    exact htneg.eventually hfac
  have hpar : ∀ᶠ ω in 𝓝[≠] (0:ℝ),(-1:ℝ)^n*g (-ω)=g ω := by
    filter_upwards [hfac.filter_mono nhdsWithin_le_nhds,hneg.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with ω hω hnω hω0
    change ω≠0 at hω0
    change limitSymbol u q (-ω)=(-ω)^n*g (-ω) at hnω
    rw [limitSymbol_even u q,neg_pow] at hnω
    apply mul_left_cancel₀ (pow_ne_zero n hω0)
    linear_combination hω-hnω
  have hleft : Tendsto (fun ω : ℝ=>(-1:ℝ)^n*g (-ω)) (𝓝[≠] (0:ℝ)) (𝓝 ((-1:ℝ)^n*g 0)) := by
    have hh := (hg.continuousAt.tendsto.comp htneg).const_mul ((-1:ℝ)^n)
    simpa only [neg_zero,Function.comp_def] using hh.mono_left nhdsWithin_le_nhds
  have hright := hg.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))
  have hpar0 : (-1:ℝ)^n*g 0=g 0 := tendsto_nhds_unique (hleft.congr' hpar) hright
  have hpow : (-1:ℝ)^n=1 := by
    apply mul_right_cancel₀ hg0
    simpa only [one_mul] using hpar0
  obtain ⟨p,hp⟩ := (neg_one_pow_eq_one_iff_even (by norm_num : (-1:ℝ)≠1)).mp hpow
  have hnp : n=2*p := by omega
  have hgeven : (fun ω : ℝ=>g (-ω))=ᶠ[𝓝 (0:ℝ)] g := by
    have hh : ∀ᶠ ω in 𝓝 (0:ℝ),ω≠0 → (-1:ℝ)^n*g (-ω)=g ω :=
      eventually_nhdsWithin_iff.mp hpar
    filter_upwards [hh] with ω hω
    by_cases hz : ω=0
    · simp only [hz,neg_zero]
    · simpa only [hpow,one_mul] using hω hz
  have hd := hg.differentiableAt.hasDerivAt
  have hnd := (show HasDerivAt g (deriv g 0) (-(0:ℝ)) by simpa only [neg_zero] using hd).comp
    0 ((hasDerivAt_id (0:ℝ)).neg)
  have hdeq := hgeven.deriv_eq
  have hdzero : deriv g 0=0 := by
    have hh : deriv (fun ω : ℝ=>g (-ω)) 0=deriv g 0*(-1) := by
      simpa only [Function.comp_def] using hnd.deriv
    rw [hh] at hdeq
    nlinarith
  obtain ⟨R,hR,he⟩ := hg.exists_eq_sum_add_pow_mul 2
  have hgexp (ω : ℝ) : g ω=g 0+ω^2*R ω := by
    have hh := he ω
    simpa only [Finset.sum_range_succ,Finset.sum_range_zero,iteratedDeriv_zero,
      iteratedDeriv_succ,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,pow_zero,pow_one,
      zero_add,div_one,one_smul,hdzero,smul_eq_mul,mul_zero,add_zero,one_mul] using hh
  have hO := (isBigO_refl (fun ω : ℝ=>ω^(2*p+2)) (𝓝 (0:ℝ))).mul
    (hR.continuousAt.isBigO (F:=ℝ))
  have hterm : HasLeadingEvenTerm u q p (g 0) := by
    refine ⟨hg0,?_⟩
    apply (hO.congr_right (fun ω=>mul_one _)).congr' ?_ (Eventually.of_forall (fun _=>rfl))
    filter_upwards [hfac] with ω hω
    rw [hω,hnp,hgexp]
    ring
  exact ⟨p,leading_even_order_ge_two hy hu hq hterm,g 0,hterm⟩

theorem leading_even_isBigO {u q : Polynomial ℝ} {p : ℕ} {s : ℝ}
    (hterm : HasLeadingEvenTerm u q p s) :
    limitSymbol u q=O[𝓝 (0:ℝ)] (fun ω : ℝ=>ω^(2*p)) := by
  have hm := (isBigO_refl (fun ω : ℝ=>ω^(2*p)) (𝓝 (0:ℝ))).const_mul_left s
  have hr := hterm.2.trans (isLittleO_pow_pow (by omega : 2*p<2*p+2)).isBigO
  exact (hm.add hr).congr_left (fun ω=>by ring)

/-- The first nonzero even term is quartic exactly away from the half-step wall. -/
theorem leading_order_two_iff {u q : Polynomial ℝ} {y : ℝ} (hy : 0<y)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) {p : ℕ} {s : ℝ}
    (hterm : HasLeadingEvenTerm u q p s) : p=2 ↔ effectiveLead u q y≠1/2 := by
  have hquartic := (symbol_quartic_ratio u q hy hu hq).mono_left (nhdsGT_le_nhdsNE (0:ℝ))
  constructor
  · intro hp hτ
    have hh := leading_even_ratio hterm
    rw [hp] at hh
    norm_num only [Nat.mul_succ,Nat.mul_one,Nat.reduceAdd] at hh
    have hs : s=(2*effectiveLead u q y-1)/(2*y) := tendsto_nhds_unique hh hquartic
    rw [hτ] at hs
    norm_num at hs
    exact hterm.1 hs
  · intro hτ
    have hp := leading_even_order_ge_two hy hu hq hterm
    by_contra hn
    have hlt : 4<2*p := by omega
    have ho := (leading_even_isBigO hterm).trans_isLittleO (isLittleO_pow_pow hlt)
    have hz := ho.tendsto_div_nhds_zero.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
    have hh : (2*effectiveLead u q y-1)/(2*y)=0 := tendsto_nhds_unique hquartic hz
    have hnume : 2*effectiveLead u q y-1=0 := (div_eq_zero_iff.mp hh).resolve_right (by positivity)
    exact hτ (by linarith)

end
end nesterov.Faithful
