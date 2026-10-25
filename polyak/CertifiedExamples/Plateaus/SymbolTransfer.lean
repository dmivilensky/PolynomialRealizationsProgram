import polyak.CertifiedExamples.Plateaus.Polynomial

/-! Transfer of certified polynomial signs to the literal dual lag symbol,
including the genuine support second jets and the endpoint moment at zero. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels ModeLocking Set Filter
open scoped Topology BigOperators

def symbolFactor (q:Tuning) (x:ℝ) : ℝ :=
  Real.sin (TwoLag.phase q 0 x)/Real.sin x*(1-Real.cos x)

theorem symbolFactor_analytic (q:Tuning) {u:ℝ} (hu:u∈Ioo (0:ℝ) Real.pi) :
    AnalyticAt ℝ (symbolFactor q) u := by
  unfold symbolFactor
  exact ((Real.analyticAt_sin.comp (TwoLag.analyticAt_phase q 0 ⟨hu.1.le,hu.2.le⟩)).div
    Real.analyticAt_sin (Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2).ne').mul
      (analyticAt_const.sub Real.analyticAt_cos)

theorem symbol_eventually_factor (q:Tuning) (N:Finset ℤ) (a:ℤ→ℝ)
    (hn:∀n∈N,n≠0) {u:ℝ} (hu:u∈Ioo (0:ℝ) Real.pi) :
    finiteSymbol q 0 N a=ᶠ[𝓝 u]
      fun x=>symbolFactor q x*polynomialSymbol q N a (Real.cos x) := by
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
  let ω:Frequency:=⟨x,hx.1.le,hx.2.le⟩
  have he:=polynomial_factor q N a hn ω hx
  change finiteSymbol q 0 N a (ω:ℝ)=symbolFactor q ω*polynomialSymbol q N a (Real.cos (ω:ℝ))
  unfold symbolFactor
  rw [TwoLag.phase_zero_actual q ω]
  exact he

theorem support_curvature_of_polynomial (q:Tuning) (N:Finset ℤ) (a:ℤ→ℝ)
    (hn:∀n∈N,n≠0) (ω:Frequency) (hω:0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi)
    (hzero:polynomialSymbol q N a (Real.cos (ω:ℝ))=0)
    (hslope:deriv (polynomialSymbol q N a) (Real.cos (ω:ℝ))=0)
    (hcurv:deriv^[2] (polynomialSymbol q N a) (Real.cos (ω:ℝ))<0) :
    deriv^[2] (finiteSymbol q 0 N a) (ω:ℝ)<0 := by
  have he:=(symbol_eventually_factor q N a hn hω).iteratedDeriv_eq 2
  simp only [iteratedDeriv_eq_iterate] at he
  rw [he]
  have hp : 0<symbolFactor q ω := by
    simpa only [symbolFactor,TwoLag.phase_zero_actual] using factor_positive q ω hω
  exact (TwoLag.second_contact_sign (symbolFactor_analytic q hω).contDiffAt
    (polynomialSymbol_analytic q N a _).contDiffAt hzero hslope hp
    (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2).ne').mpr hcurv

private theorem dividedLag_endpoint (q:Tuning) (n:ℤ) (hn:n≠0) :
    dividedLag q n 1=q.Xi 1*(n:ℝ)*((n:ℝ)+2*Geometry.tau q) := by
  have habs : 1≤n.natAbs := by
    have hp:=Int.natAbs_pos.mpr hn
    omega
  have hu : Spectral.chebU (n.natAbs-1) 1=(n.natAbs:ℝ) := by
    simp only [Spectral.chebU,Polynomial.Chebyshev.U_eval_one,Int.cast_natCast]
    rw [Nat.cast_sub habs]
    ring
  have hsign : (n.sign:ℝ)*(n.natAbs:ℝ)=(n:ℝ) := by
    rw [Nat.cast_natAbs,←Int.cast_mul]
    exact_mod_cast Int.sign_mul_natAbs n
  have hsq : (n.natAbs:ℝ)^2=(n:ℝ)^2 := by
    rw [Nat.cast_natAbs,Int.cast_abs,sq_abs]
  unfold dividedLag
  rw [TwoLag.W_one,hu]
  have hXi:=q.Xi_one_neg.ne
  unfold Geometry.tau
  field_simp
  linear_combination q.Xi 1*hsq-2*hsign

theorem endpoint_moment_of_polynomial (q:Tuning) (N:Finset ℤ) (a:ℤ→ℝ)
    (hn:∀n∈N,n≠0) (hneg:polynomialSymbol q N a 1<0) :
    0<∑n∈N,a n*(n:ℝ)*((n:ℝ)+2*Geometry.tau q) := by
  have he : polynomialSymbol q N a 1=
      q.Xi 1*(∑n∈N,a n*(n:ℝ)*((n:ℝ)+2*Geometry.tau q)) := by
    unfold polynomialSymbol
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hmem
    rw [dividedLag_endpoint q n (hn n hmem)]
    ring
  rw [he] at hneg
  exact pos_of_mul_neg_right hneg q.Xi_one_neg.le

theorem finiteSymbol_pi_negative (q:Tuning) (N:Finset ℤ) (a:ℤ→ℝ)
    (ha:∀n∈N,0≤a n) (h1:1∈N) (ha1:0<a 1) : finiteSymbol q 0 N a Real.pi<0 := by
  have he := finiteSymbol_actual q 0 N a frequencyPi
  change finiteSymbol q 0 N a Real.pi=_ at he
  rw [he,Geometry.shiftedCurve_zero]
  apply neg_pos.mp
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_pos'
  · intro n hn
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (ha n hn) ((tuningCurve q).lag_at_pi_nonpos n))
  · refine ⟨1,h1,?_⟩
    have hLag : (tuningCurve q).lag 1 frequencyPi= -2 := by
      rw [Curve.lag_at_pi]
      norm_num
    rw [hLag]
    linarith

theorem full_symbol_strict (q:Tuning) (N:Finset ℤ) (a:ℤ→ℝ)
    (hn:∀n∈N,n≠0) (ha:∀n∈N,0≤a n) (h1:1∈N) (ha1:0<a 1)
    (Z:Finset Frequency)
    (hpoly:∀c∈Icc (-1:ℝ) 1,(∀ω∈Z,c≠Real.cos (ω:ℝ))→polynomialSymbol q N a c<0)
    {x:ℝ} (hx:0<x ∧ x≤Real.pi) (haway:∀ω∈Z,x≠(ω:ℝ)) :
    finiteSymbol q 0 N a x<0 := by
  by_cases hp:x=Real.pi
  · subst x
    exact finiteSymbol_pi_negative q N a ha h1 ha1
  · have hi : x∈Ioo (0:ℝ) Real.pi:=⟨hx.1,lt_of_le_of_ne hx.2 hp⟩
    let ω:Frequency:=⟨x,hx.1.le,hx.2⟩
    apply polynomial_strict q N a hn ω hi
    apply hpoly (Real.cos x) ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
    intro z hz he
    exact haway z hz (Real.strictAntiOn_cos.injOn ⟨hx.1.le,hx.2⟩ z.property he)

end polyak.CertifiedExamples.Plateaus
