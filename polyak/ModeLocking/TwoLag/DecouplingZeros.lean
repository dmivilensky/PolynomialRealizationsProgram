import polyak.ModeLocking.TwoLag.Decoupling

/-! Zero sets of a nonnegative two-lag dual consist exactly of the two
independent ratio maxima; the minimizer multiplier is forced to vanish. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open Levels Set

theorem pair_zero_iff_ratio {Θ : Curve} {K : ℕ} (hno : NoCommonNonnegative Θ K)
    {a b : ℝ} (ha : 0<a) (hb : 0<b) (ω : Frequency) (hx : 0<(ω : ℝ)) :
    (a*Θ.lag 1 ω+b*Θ.lag (-(K : ℤ)) ω=0) ↔
      (ω∈plusSet Θ K ∧ plusRatio Θ K ω=b/a) ∨
      (ω∈minusSet Θ K ∧ minusRatio Θ K ω=a/b) := by
  constructor
  · intro hz
    by_cases hp : 0<Θ.lag 1 ω
    · have hn : Θ.lag (-(K : ℤ)) ω<0 := by
        by_contra hn
        have hm := mul_nonneg hb.le (le_of_not_gt hn)
        nlinarith [mul_pos ha hp]
      left
      refine ⟨⟨hp,hn⟩,?_⟩
      apply (div_eq_div_iff (neg_ne_zero.mpr hn.ne) ha.ne').mpr
      nlinarith [hz]
    · have hn : Θ.lag 1 ω<0 := by
        apply lt_of_le_of_ne (le_of_not_gt hp)
        intro he
        have hzK : Θ.lag (-(K : ℤ)) ω=0 := by
          rw [he,mul_zero,zero_add] at hz
          exact (mul_eq_zero.mp hz).resolve_left hb.ne'
        exact hno ω hx ⟨by rw [he],by rw [hzK]⟩
      have hpK : 0<Θ.lag (-(K : ℤ)) ω := by
        by_contra h
        have hm := mul_nonpos_of_nonneg_of_nonpos hb.le (le_of_not_gt h)
        nlinarith [mul_neg_of_pos_of_neg ha hn]
      right
      refine ⟨⟨hpK,hn⟩,?_⟩
      apply (div_eq_div_iff (neg_ne_zero.mpr hn.ne) hb.ne').mpr
      nlinarith [hz]
  · rintro (⟨hω,hr⟩|⟨hω,hr⟩)
    · have hh := (div_eq_div_iff (neg_ne_zero.mpr hω.2.ne) ha.ne').mp hr
      nlinarith [hh]
    · have hh := (div_eq_div_iff (neg_ne_zero.mpr hω.2.ne) hb.ne').mp hr
      nlinarith [hh]

/-- Full dual conclusion in Proposition decouple(b). -/
theorem decoupling_dual {Θ : Curve} {K : ℕ} (hK : 2≤K)
    (hno : NoCommonNonnegative Θ K) (M : PlusMaximum Θ K)
    {v : Frequency} (hv : v∈minusSet Θ K) (hmin : 0<Θ.minimizer v)
    (hmax : ∀ω∈minusSet Θ K,minusRatio Θ K ω≤minusRatio Θ K v)
    (hfp : FPOn Θ (pairLags K)) {a b γ : ℝ} (ha : 0≤a) (hb : 0≤b) (hγ : 0≤γ)
    (hne : a≠0 ∨ b≠0 ∨ γ≠0)
    (hS : ∀ω,a*Θ.lag 1 ω+b*Θ.lag (-(K : ℤ)) ω+γ*Θ.minimizer ω≤0) :
    γ=0 ∧ 0<a ∧ 0<b ∧ M.value=b/a ∧ minusRatio Θ K v=a/b ∧
      ∀ω : Frequency,0<(ω : ℝ)→
        (a*Θ.lag 1 ω+b*Θ.lag (-(K : ℤ)) ω+γ*Θ.minimizer ω=0 ↔
          (ω∈plusSet Θ K ∧ plusRatio Θ K ω=M.value) ∨
          (ω∈minusSet Θ K ∧ minusRatio Θ K ω=minusRatio Θ K v)) := by
  have hp := (decoupling_feasible_iff hK hno M hv hmin hmax).mp hfp
  have hplus : (plusSet Θ K).Nonempty := by
    by_contra hn
    rw [M.empty_zero (Set.not_nonempty_iff_eq_empty.mp hn),zero_mul] at hp
    norm_num at hp
  obtain ⟨u,hu,hMu⟩ := M.attained hplus
  obtain ⟨r,hr,hsol,hslack⟩ := feasible_of_ratio_product hu hv hmin (by rwa [hMu])
  have hlag1 := hsol.2.2.2 1 (by simp [pairLags])
  have hlagK := hsol.2.2.2 (-(K : ℤ)) (by simp [pairLags])
  rw [pairMeasure_integral] at hlag1 hlagK hslack
  have hsum : a*(Θ.lag 1 u+(r : ℝ)*Θ.lag 1 v)+
      b*(Θ.lag (-(K : ℤ)) u+(r : ℝ)*Θ.lag (-(K : ℤ)) v)+
      γ*(Θ.minimizer u+(r : ℝ)*Θ.minimizer v)≤0 := by
    have hweighted := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℝ)≤r from r.coe_nonneg) (hS v)
    nlinarith [hS u,hweighted]
  have hγzero : γ=0 := by
    have h0 := mul_nonneg ha hlag1
    have h1 := mul_nonneg hb hlagK
    have h2 := mul_nonneg hγ hslack.le
    have hz : γ*(Θ.minimizer u+(r : ℝ)*Θ.minimizer v)=0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_right hslack.ne'
  have hSu : a*Θ.lag 1 u+b*Θ.lag (-(K : ℤ)) u≤0 := by simpa [hγzero] using hS u
  have hSv : a*Θ.lag 1 v+b*Θ.lag (-(K : ℤ)) v≤0 := by simpa [hγzero] using hS v
  have htotal : a*Θ.lag 1 u+b*Θ.lag (-(K : ℤ)) u+
      (r : ℝ)*(a*Θ.lag 1 v+b*Θ.lag (-(K : ℤ)) v)=0 := by
    nlinarith [mul_nonneg ha hlag1,mul_nonneg hb hlagK,
      mul_nonpos_of_nonneg_of_nonpos r.coe_nonneg hSv]
  have hzeroU : a*Θ.lag 1 u+b*Θ.lag (-(K : ℤ)) u=0 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos r.coe_nonneg hSv]
  have hzeroV : a*Θ.lag 1 v+b*Θ.lag (-(K : ℤ)) v=0 := by
    have hr' : (0 : ℝ)<r := hr
    have hz : (r : ℝ)*(a*Θ.lag 1 v+b*Θ.lag (-(K : ℤ)) v)=0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left hr'.ne'
  have ha' : 0<a := by
    apply lt_of_le_of_ne ha
    intro hzero
    have ha0 : a=0 := hzero.symm
    have hbzero : b=0 := by
      rw [ha0,zero_mul,zero_add] at hzeroU
      exact (mul_eq_zero.mp hzeroU).resolve_right hu.2.ne
    rcases hne with h|h|h
    · exact h ha0
    · exact h hbzero
    · exact h hγzero
  have hb' : 0<b := by
    apply lt_of_le_of_ne hb
    intro hzero
    have hb0 : b=0 := hzero.symm
    rw [hb0,zero_mul,add_zero] at hzeroU
    exact (mul_pos ha' hu.1).ne' hzeroU
  have hRplus : M.value=b/a := by
    rw [←hMu]
    apply (div_eq_div_iff (neg_ne_zero.mpr hu.2.ne) ha'.ne').mpr
    nlinarith [hzeroU]
  have hRminus : minusRatio Θ K v=a/b := by
    apply (div_eq_div_iff (neg_ne_zero.mpr hv.2.ne) hb'.ne').mpr
    nlinarith [hzeroV]
  refine ⟨hγzero,ha',hb',hRplus,hRminus,?_⟩
  intro ω hx
  rw [hγzero,zero_mul,add_zero,hRplus,hRminus]
  exact pair_zero_iff_ratio hno ha' hb' ω hx

end polyak.ModeLocking.TwoLag
