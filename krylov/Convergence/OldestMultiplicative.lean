import krylov.Convergence.WindowSharpQuery

/-!
Article: main_krylov, thm:Ip, precise multiplicative oldest estimate.
Use: package a proved additive newer-age remainder as the literal printed
1+o(1) factor when the Hessian Lipschitz allowance is positive. Source:
bounded actual inverse distances and elementary relative little-o calculus.
-/
namespace krylov.Convergence
noncomputable section
open Filter Topology Asymptotics
set_option maxHeartbeats 800000

/-- Actual separated distances turn the complete oldest-diagonal source
bound into its literal multiplicative asymptotic form, including zero
values of the error sequence. -/
theorem oldest_multiplicative_factor (q q₁ D m r : ℕ → ℝ)
    {σ L : ℝ} (hσ : 0<σ) (hL : 0<L) (hq : ∀ k,0≤q k)
    (hD : ∀ᶠ k in atTop,σ≤D k ∧D k≤1)
    (hm : Tendsto m atTop (𝓝 1)) (hq₁ : q₁=o[atTop] q) (hr : r=o[atTop] q) :
    ∃ theta : ℕ → ℝ,Tendsto theta atTop (𝓝 0) ∧∀ᶠ k in atTop,
      m k*((L/2*(q k+q₁ k))/(D k)^2+r k)=
        (1+theta k)*(L/(2*(D k)^2))*q k := by
  let B := fun k=>((D k)^2)⁻¹
  let a := fun k=>L/2*q k*B k
  let R := fun k=>L/2*q₁ k*B k+r k
  have hB : B=O[atTop](fun _=>(1:ℝ)) := by
    apply IsBigO.of_bound ((σ^2)⁻¹)
    filter_upwards [hD] with k hk
    have hs := pow_le_pow_left₀ hσ.le hk.1 2
    have hh := inv_anti₀ (sq_pos_of_pos hσ) hs
    simpa only [B,Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _)),norm_one,mul_one] using hh
  have hR : R=o[atTop] q := by
    have hh := (hq₁.const_mul_left (L/2)).mul_isBigO hB
    simp only [mul_one] at hh
    exact hh.add hr
  have hqa : q=O[atTop] a := by
    apply IsBigO.of_bound (2/L)
    filter_upwards [hD] with k hk
    have hdpos : 0<D k := hσ.trans_le hk.1
    have hdle : (D k)^2≤1 := by nlinarith only [hk.2,hdpos]
    have hinv : 1≤B k := by
      have hh := inv_anti₀ (sq_pos_of_pos hdpos) hdle
      simpa only [inv_one] using hh
    have ha : 0≤a k := mul_nonneg (mul_nonneg (by positivity) (hq k))
      (inv_nonneg.mpr (sq_nonneg _))
    rw [Real.norm_of_nonneg (hq k),Real.norm_of_nonneg ha]
    have hh := mul_le_mul_of_nonneg_left hinv (hq k)
    have heq : (2/L)*(L/2*q k*B k)=q k*B k := by
      field_simp
    simpa only [a,heq,mul_one] using hh
  obtain ⟨theta,htheta,he⟩ := littleo_relative_factor a R (hR.trans_isBigO hqa)
  refine ⟨fun k=>m k*(1+theta k)-1,?_,?_⟩
  · have hconst : Tendsto (fun _ : ℕ=>(1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hh := (hm.mul (hconst.add htheta)).sub hconst
    simpa only [add_zero,mul_one,sub_self] using hh
  filter_upwards [he] with k hk
  have hh := congrArg (fun z=>m k*z) hk
  dsimp only [a,R,B] at hh
  convert hh using 1 <;> ring

end
end krylov.Convergence
