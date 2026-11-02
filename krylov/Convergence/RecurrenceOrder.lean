import krylov.Convergence.Order
import krylov.Convergence.CharacteristicRoots

/-!
Article: main_krylov, lem:rorder2(a,b).
Use: derive the exact characteristic R-orders from eventual genuine scalar
error recursions. Direct exponential barriers admit zero errors as well as
strictly positive errors; no logarithm of an error is required.
Source: Ortega and Rheinboldt (1970), characteristic supersolution induction.
-/

/-!
Article: krylov, Lemma E.3 [lem:rorder2].

Delayed product and corrected recurrences imply the actual exponential-barrier R-order, with no
rate assumed as a record field.
The root definition matches the two delayed indices; zero errors, stationary tails and finite-
prefix shifts are handled in the formal recurrence theorems.
-/
namespace krylov.Convergence
noncomputable section
open Filter Topology

/-- The characteristic identity propagates the two delayed exponential
barriers exactly. Article: main_krylov, lem:rorder2(a). -/
theorem secantRoot_delayed_powers (p q j : ℕ) (hq : q≤p) (hj : p+1≤j) :
    secantRoot p q^j=secantRoot p q^(j-1-p)+secantRoot p q^(j-1-q) := by
  have h := secantRoot_equation p q hq
  have hp : j=(j-1-p)+(p+1) := by omega
  have hq' : j-1-q=(j-1-p)+(p-q) := by omega
  calc
    secantRoot p q^j=secantRoot p q^(j-1-p)*secantRoot p q^(p+1) := by rw [←pow_add,←hp]
    _ = secantRoot p q^(j-1-p)*(secantRoot p q^(p-q)+1) := by rw [h]
    _ = _ := by rw [hq',pow_add]; ring

/-- A genuine two-lag product recurrence implies the unique printed
characteristic R-order. This strengthens the original positive-error lemma
by including exact stationary and intermittent zero errors.
Article: main_krylov, lem:rorder2(a). -/
theorem rorder_product_recurrence (e : ℕ → ℝ) (he : ∀ k,0≤e k)
    (hconv : Tendsto e atTop (𝓝 0)) (p q : ℕ) (hq : q≤p)
    (hrec : ∃ K : ℝ,0<K ∧ ∀ᶠ k in atTop,e (k+1)≤K*e (k-p)*e (k-q)) :
    HasROrder e (secantRoot p q) := by
  obtain ⟨K,hK,hrec⟩ := hrec
  let τ := secantRoot p q
  have hτ : 1<τ := secantRoot_gt_one p q
  have hτ₀ : 0<τ := zero_lt_one.trans hτ
  have hsmall : ∀ᶠ k in atTop,e k<Real.exp (-1)/K :=
    hconv.eventually (gt_mem_nhds (div_pos (Real.exp_pos _) hK))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hrec.and hsmall)
  let c := (τ^p)⁻¹
  have hc : 0<c := inv_pos.mpr (pow_pos hτ₀ p)
  have hbound (j : ℕ) : K*e (N+j)≤Real.exp (-c*τ^j) := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      by_cases hj : j≤p
      · have hb := (lt_div_iff₀ hK).mp (hN (N+j) (Nat.le_add_right _ _)).2
        have hexp : c*τ^j≤1 := by
          have hh := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hτ.le hj) hc.le
          simpa only [c,inv_mul_cancel₀ (pow_pos hτ₀ p).ne'] using hh
        have hx : Real.exp (-1)≤Real.exp (-c*τ^j) :=
          Real.exp_le_exp.mpr (by linarith only [hexp])
        exact (by nlinarith only [hb] : K*e (N+j)≤Real.exp (-1)).trans hx
      · have hjp : j-1-p<j := by omega
        have hjq : j-1-q<j := by omega
        have hp := ih (j-1-p) hjp
        have hq' := ih (j-1-q) hjq
        have hr := (hN (N+j-1) (by omega)).1
        have hpidx : N+j-1-p=N+(j-1-p) := by omega
        have hqidx : N+j-1-q=N+(j-1-q) := by omega
        have hnew : N+j-1+1=N+j := by omega
        rw [hpidx,hqidx,hnew] at hr
        have hh := mul_le_mul hp hq' (mul_nonneg hK.le (he _)) (Real.exp_pos _).le
        calc
          K*e (N+j)≤(K*e (N+(j-1-p)))*(K*e (N+(j-1-q))) := by
            have hh' := mul_le_mul_of_nonneg_left hr hK.le
            nlinarith only [hh']
          _ ≤ Real.exp (-c*τ^(j-1-p))*Real.exp (-c*τ^(j-1-q)) := hh
          _ = Real.exp (-c*τ^j) := by
            rw [←Real.exp_add,secantRoot_delayed_powers p q j hq (by omega)]
            congr 1
            ring
  apply hasROrder_of_tail_exp e τ hτ₀ N (inv_pos.mpr hK) hc
  intro j
  have hh := mul_le_mul_of_nonneg_left (hbound j) (inv_nonneg.mpr hK.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hK.ne',one_mul] using hh

/-- A positive integral cycle degree yields the genuine restarted R-order,
including zero errors. Article: main_krylov, thm:D and Table s7-orders. -/
theorem rorder_power_recurrence (e : ℕ → ℝ) (he : ∀ k,0≤e k)
    (hconv : Tendsto e atTop (𝓝 0)) (d : ℕ) (hd : 2≤d)
    (hrec : ∃ C : ℝ,0<C ∧ ∀ᶠ k in atTop,e (k+1)≤C*(e k)^d) :
    HasROrder e (d : ℝ) := by
  obtain ⟨C,hC,hrec⟩ := hrec
  let K := C+1
  have hK : 0<K := by dsimp only [K]; positivity
  have hKC : K*C≤K^d := by
    have hsq : K*C≤K^2 := by dsimp only [K]; nlinarith only [hC]
    exact hsq.trans (pow_le_pow_right₀ (by dsimp only [K]; linarith only [hC]) hd)
  have hsmall : ∀ᶠ k in atTop,e k<Real.exp (-1)/K :=
    hconv.eventually (gt_mem_nhds (div_pos (Real.exp_pos _) hK))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hrec.and hsmall)
  have hb (j : ℕ) : K*e (N+j)≤Real.exp (-((d : ℝ)^j)) := by
    induction j with
    | zero =>
      have hh := (lt_div_iff₀ hK).mp (hN N le_rfl).2
      simp only [Nat.add_zero,pow_zero]
      nlinarith only [hh]
    | succ j ih =>
      have hr := (hN (N+j) (Nat.le_add_right _ _)).1
      calc
        K*e (N+(j+1))≤K*(C*(e (N+j))^d) := by
          simpa only [Nat.add_assoc] using mul_le_mul_of_nonneg_left hr hK.le
        _ ≤ K^d*(e (N+j))^d := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hKC (pow_nonneg (he _) d)
        _ = (K*e (N+j))^d := (mul_pow _ _ _).symm
        _ ≤ (Real.exp (-((d : ℝ)^j)))^d := pow_le_pow_left₀ (mul_nonneg hK.le (he _)) ih _
        _ = Real.exp (-((d : ℝ)^(j+1))) := by
          rw [←Real.exp_nat_mul,pow_succ]
          congr 1
          ring
  apply hasROrder_of_tail_exp e (d : ℝ) (by positivity) N (inv_pos.mpr hK) zero_lt_one
  intro j
  have hh := mul_le_mul_of_nonneg_left (hb j) (inv_nonneg.mpr hK.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hK.ne',one_mul,neg_one_mul] using hh

end
end krylov.Convergence
