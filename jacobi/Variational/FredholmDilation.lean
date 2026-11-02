import jacobi.Variational.StrictDilation

/-!
Article: jacobi, Appendix D.1 (strict concentration gain).
Isolating the leading coefficient of the actual nonnegative Fredholm series
transfers the proved strict G_2 gain to the full determinant, including its
infinite values. A sufficiently small radial dilation stays below a proved
spectral pole margin, so the same gain applies to the real finite functional.
Source: Tonelli for nonnegative series and L1 spectral stability.
Use: the strict G_2 dilation gain propagates to the entire determinant, including poles.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter chebyshev2.Continuum
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The first Fredholm coefficient controls the gain whenever every actual cyclic moment increases.
Use: the strict G_2 dilation gain propagates to the entire determinant, including poles.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: split the nonnegative Fredholm series into its G_2 term and its tail;
compare all tail terms and combine the finite leading real terms exactly. -/
theorem fredholm_moment_gain (m q : L1Source) {s : ℝ} (hs : 0≤s)
    (hmq : ∀ n : ℕ,(∑' j,m.spectrum j^(n+2))≤∑' j,q.spectrum j^(n+2)) :
    m.fredholm s+ENNReal.ofReal (s^2/2*(observe q .second-observe m .second))≤q.fredholm s := by
  -- No subtraction of infinite determinant values is used.
  let F (v : L1Source) (n : ℕ) := ENNReal.ofReal (s^(n+2)/((n:ℝ)+2))*
    ENNReal.ofReal (∑' j,v.spectrum j^(n+2))
  have hsplit (v : L1Source) : v.fredholm s=ENNReal.ofReal (s^2/2*observe v .second)+
      ∑' n : ℕ,F v (n+1) := by
    rw [v.fredholm_series hs,tsum_eq_zero_add' ENNReal.summable]
    congr 1
    simp only [Nat.cast_zero,zero_add]
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ)≤s^2/2)]
    rfl
  have htail : (∑' n : ℕ,F m (n+1))≤∑' n : ℕ,F q (n+1) := by
    apply ENNReal.tsum_le_tsum
    intro n
    exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hmq (n+1))) (by positivity)
  have hG : observe m .second≤observe q .second := hmq 0
  have hmG : 0≤observe m .second := tsum_nonneg fun j => sq_nonneg _
  have hadd : ENNReal.ofReal (s^2/2*observe m .second)+
      ENNReal.ofReal (s^2/2*(observe q .second-observe m .second))=
      ENNReal.ofReal (s^2/2*observe q .second) := by
    rw [← ENNReal.ofReal_add (mul_nonneg (by positivity) hmG)
      (mul_nonneg (by positivity) (sub_nonneg.mpr hG))]
    congr 1
    ring
  rw [hsplit m,hsplit q,add_right_comm,hadd]
  exact add_le_add le_rfl htail

/-- The actual extended Fredholm functional has a positive linear concentration gain.
Use: proves strict dilation even when the concentration reaches or crosses a spectral pole.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: retain the proved strict G_2 gain and the monotonicity of every higher cyclic moment. -/
theorem fredholm_strict_dilation_extended (m : L1Source) (hm : 0<m.mass) {s : ℝ} (hs : 0<s) :
    ∃ k : ℝ,0<k ∧ ∀ (t : ℝ) (ht : 1≤t),t≤2 →
      m.fredholm s+ENNReal.ofReal (k*(t-1))≤(m.dilate t (by linarith)).fredholm s := by
  -- Positivity is inherited from the actual nonzero density's strictly positive G_2 gain.
  obtain ⟨c,hc,hgain⟩ := second_strict_dilation m hm
  refine ⟨s^2/2*c,by positivity,fun t ht ht2 => ?_⟩
  have h := fredholm_moment_gain m (m.dilate t (by linarith)) hs.le (fun n => by
    simpa only [Nat.add_assoc] using dilate_moment_mono m (n+1) ht)
  apply le_trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)) h
  have hG := hgain t ht ht2
  nlinarith [sq_nonneg s]

/-- A short radial concentration keeps the actual top spectrum uniformly below the pole.
Use: turns the extended strict Fredholm gain into the finite first-variation regularity direction.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: choose a positive radius from the original pole gap and combine the
printed radial L1 dilation bound with actual top-eigenvalue L1 stability. -/
theorem dilation_pole_margin (m : L1Source) (hm : 0<m.mass) (hrad : SymmetricDecreasing m.value)
    {s : ℝ} (hs : 0<s) (hp : s*observe m .top<1) :
    ∃ η : ℝ,0<η ∧ ∀ (t : ℝ) (ht : 1≤t),t≤1+η →
      s*observe (m.dilate t (by linarith)) .top≤1-(1-s*observe m .top)/2 := by
  -- The radius depends on the actual pole gap, not on a stronger small-mass condition.
  let η := (1-s*observe m .top)/(4*s*m.mass)
  have hη : 0<η := div_pos (sub_pos.mpr hp) (by positivity)
  refine ⟨η,hη,fun t ht htη => ?_⟩
  let q := m.dilate t (by linarith)
  have htop := kernel_top_distance q.integrable m.integrable q.nonneg m.nonneg
  change |observe q .top-observe m .top|≤_ at htop
  have hL := dilation_l1 m hrad ht
  have hb := (le_abs_self (observe q .top-observe m .top)).trans (htop.trans hL)
  have hηeq : 4*s*m.mass*η=1-s*observe m .top := by
    dsimp only [η]
    field_simp
  have hmult := mul_le_mul_of_nonneg_left (show t-1≤η by linarith) (by positivity : 0≤2*s*m.mass)
  nlinarith [mul_le_mul_of_nonneg_left hb hs.le]

/-- The actual finite Fredholm functional satisfies the multiplier rule's strict dilation hypothesis.
Use: provides both finiteness and a positive linear gain along one mass-preserving radial perturbation family.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: intersect the small spectral-margin interval with [1,2], identify the
extended values with their genuine finite real branches, and remove ofReal. -/
theorem fredholm_strict_dilation (m : L1Source) (hm : 0<m.mass) (hrad : SymmetricDecreasing m.value)
    {s : ℝ} (hs : 0<s) (hp : s*observe m .top<1) :
    ∃ k η : ℝ,0<k ∧ 0<η ∧ ∀ (t : ℝ) (ht : 1≤t),t≤1+η →
      s*observe (m.dilate t (by linarith)) .top<1 ∧
      m.fredholmReal s+k*(t-1)≤(m.dilate t (by linarith)).fredholmReal s := by
  -- Both determinant values are proved finite on the chosen interval before real subtraction.
  obtain ⟨k,hk,hgain⟩ := fredholm_strict_dilation_extended m hm hs
  obtain ⟨η,hη,hmargin⟩ := dilation_pole_margin m hm hrad hs hp
  refine ⟨k,min η 1,hk,lt_min hη zero_lt_one,fun t ht htη => ?_⟩
  have ht2 : t≤2 := by linarith [min_le_right η 1]
  have hmq := hmargin t ht (by linarith [min_le_left η 1])
  have hε : 0<(1-s*observe m .top)/2 := by linarith
  let q := m.dilate t (by linarith)
  have hpm : s*observe m .top≤1-(1-s*observe m .top)/2 := by linarith
  have hext := hgain t ht ht2
  rw [m.fredholm_eq hs.le hε hpm,q.fredholm_eq hs.le hε hmq] at hext
  have hmnon : 0≤m.fredholmReal s := tsum_nonneg fun j =>
    fredholmLog_nonneg (by have h := m.spectral_margin hs.le hpm j; linarith)
  rw [← ENNReal.ofReal_add hmnon (mul_nonneg hk.le (sub_nonneg.mpr ht))] at hext
  have hqnon : 0≤q.fredholmReal s := tsum_nonneg fun j =>
    fredholmLog_nonneg (by have h := q.spectral_margin hs.le hmq j; linarith)
  refine ⟨by linarith,?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff hqnon).mp hext

end
end jacobi.Variational
