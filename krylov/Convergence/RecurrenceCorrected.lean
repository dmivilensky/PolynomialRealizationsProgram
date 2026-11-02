import krylov.Convergence.RecurrenceOrder

/-!
Article: main_krylov, lem:rorder2(b), the corrected secant recurrence.
Use: prove the genuine improved one-gradient R-order from the two-term
trapezoid recurrence, including every zero error and the case m=1.
Source: Ortega--Rheinboldt exponential barriers and the exact characteristic
identity; the extra cubic term has a no-smaller barrier exponent.
-/
namespace krylov.Convergence
noncomputable section
open Filter Topology

/-- The corrected characteristic barrier treats the recent product exactly.
Article: main_krylov, lem:rorder2(b). -/
theorem oneGradientRoot_delayed_powers (m j : ℕ) (hm : 0<m) (hj : m≤j) :
    oneGradientRoot m^j=oneGradientRoot m^(j-1)+oneGradientRoot m^(j-m) := by
  have he := oneGradientRoot_equation hm
  have hfirst : j=(j-m)+m := by omega
  have hsecond : j-1=(j-m)+(m-1) := by omega
  calc
    oneGradientRoot m^j=oneGradientRoot m^(j-m)*oneGradientRoot m^m := by rw [←pow_add,←hfirst]
    _ = _ := by rw [he,mul_add,mul_one,←pow_add,←hsecond]

/-- The older squared term has at least the improved characteristic exponent.
Article: main_krylov, lem:rorder2(b). -/
theorem oneGradientRoot_old_exponent (m j : ℕ) (hm : 0<m) (hj : m+1≤j) :
    oneGradientRoot m^j≤oneGradientRoot m^(j-1)+2*oneGradientRoot m^(j-1-m) := by
  rw [oneGradientRoot_delayed_powers m j hm (by omega)]
  have he : j-m=(j-1-m)+1 := by omega
  rw [he,pow_succ]
  have hτ := secantRoot_le_two (m-1) 0
  have hp : 0≤oneGradientRoot m^(j-1-m) :=
    pow_nonneg (le_trans zero_le_one (secantRoot_gt_one (m-1) 0).le) _
  change oneGradientRoot m≤2 at hτ
  nlinarith only [mul_le_mul_of_nonneg_left hτ hp]

/-- The actual two-term corrected recurrence implies the improved root
order tau_1(m), with no strictly-positive-error assumption.
Article: main_krylov, lem:rorder2(b), including m=1 and stationary errors. -/
theorem rorder_corrected_recurrence (e : ℕ → ℝ) (he : ∀ k,0≤e k)
    (hconv : Tendsto e atTop (𝓝 0)) (m : ℕ) (hm : 0<m)
    (hrec : ∃ K : ℝ,0<K ∧ ∀ᶠ k in atTop,
      e (k+1)≤K*e k*(e (k-m+1)+(e (k-m))^2)) :
    HasROrder e (oneGradientRoot m) := by
  obtain ⟨K,hK,hrec⟩ := hrec
  let A := 2*K+1
  have hA : 0<A := by dsimp only [A]; positivity
  have hcoeff : A*K≤A^2/2 := by dsimp only [A]; nlinarith only [hK]
  have hcoeff₂ : A*K≤A^3/2 := by
    have hh : A^2≤A^3 := pow_le_pow_right₀ (by dsimp only [A]; linarith only [hK]) (by norm_num)
    linarith only [hcoeff,hh]
  let τ := oneGradientRoot m
  have hτ : 1<τ := secantRoot_gt_one (m-1) 0
  have hτ₀ : 0<τ := zero_lt_one.trans hτ
  have hsmall : ∀ᶠ k in atTop,e k<Real.exp (-1)/A :=
    hconv.eventually (gt_mem_nhds (div_pos (Real.exp_pos _) hA))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hrec.and hsmall)
  let c := (τ^m)⁻¹
  have hc : 0<c := inv_pos.mpr (pow_pos hτ₀ m)
  have hbound (j : ℕ) : A*e (N+j)≤Real.exp (-c*τ^j) := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      by_cases hj : j≤m
      · have hb := (lt_div_iff₀ hA).mp (hN (N+j) (Nat.le_add_right _ _)).2
        have hexp : c*τ^j≤1 := by
          have hh := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hτ.le hj) hc.le
          simpa only [c,inv_mul_cancel₀ (pow_pos hτ₀ m).ne'] using hh
        have hx : Real.exp (-1)≤Real.exp (-c*τ^j) :=
          Real.exp_le_exp.mpr (by linarith only [hexp])
        exact (by nlinarith only [hb] : A*e (N+j)≤Real.exp (-1)).trans hx
      · have h₀ := ih (j-1) (by omega)
        have h₁ := ih (j-m) (by omega)
        have h₂ := ih (j-1-m) (by omega)
        have hr := (hN (N+j-1) (by omega)).1
        rw [show N+j-1+1=N+j by omega,
          show N+j-1-m+1=N+(j-m) by omega,
          show N+j-1-m=N+(j-1-m) by omega] at hr
        have hnew : A*e (N+j)≤
            (1/2:ℝ)*(A*e (N+(j-1)))*(A*e (N+(j-m)))+
              (1/2:ℝ)*(A*e (N+(j-1)))*(A*e (N+(j-1-m)))^2 := by
          have hr' := mul_le_mul_of_nonneg_left hr hA.le
          have ha := mul_le_mul_of_nonneg_right hcoeff
            (mul_nonneg (he (N+j-1)) (he (N+(j-m))))
          have hb := mul_le_mul_of_nonneg_right hcoeff₂
            (mul_nonneg (he (N+j-1)) (sq_nonneg (e (N+(j-1-m)))))
          rw [show N+j-1=N+(j-1) by omega] at hr' ha hb
          nlinarith only [hr',ha,hb]
        have hp₁ := mul_le_mul h₀ h₁ (mul_nonneg hA.le (he _)) (Real.exp_pos _).le
        have hp₂ := mul_le_mul h₀
          (pow_le_pow_left₀ (mul_nonneg hA.le (he _)) h₂ 2)
          (sq_nonneg _) (Real.exp_pos _).le
        have he₁ : Real.exp (-c*τ^(j-1))*Real.exp (-c*τ^(j-m))=Real.exp (-c*τ^j) := by
          rw [←Real.exp_add,oneGradientRoot_delayed_powers m j hm (by omega)]
          congr 1
          ring
        have he₂ : Real.exp (-c*τ^(j-1))*(Real.exp (-c*τ^(j-1-m)))^2≤Real.exp (-c*τ^j) := by
          rw [←Real.exp_nat_mul,←Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hh := mul_le_mul_of_nonneg_left (oneGradientRoot_old_exponent m j hm (by omega)) hc.le
          change c*τ^j≤c*(τ^(j-1)+2*τ^(j-1-m)) at hh
          norm_num only [Nat.cast_ofNat]
          nlinarith only [hh]
        have hh := add_le_add (mul_le_mul_of_nonneg_left (hp₁.trans_eq he₁) (by norm_num : (0:ℝ)≤1/2))
          (mul_le_mul_of_nonneg_left (hp₂.trans he₂) (by norm_num : (0:ℝ)≤1/2))
        exact hnew.trans (by nlinarith only [hh])
  apply hasROrder_of_tail_exp e τ hτ₀ N (inv_pos.mpr hA) hc
  intro j
  have hh := mul_le_mul_of_nonneg_left (hbound j) (inv_nonneg.mpr hA.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hA.ne',one_mul] using hh

end
end krylov.Convergence
