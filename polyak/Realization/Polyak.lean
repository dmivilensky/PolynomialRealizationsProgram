import polyak.Realization.Startup
import polyak.Waves.Polyak

/-!
Article: Appendix A, Polyak's one-coordinate initialization at τ=0.
Use: retain the explicit scalar response rather than an unspecified generic coefficient.
Proof: the even and odd responses are powers of -q², hence every positive-time response has modulus below one.
-/

namespace polyak.Realization
noncomputable section
open Waves Spectral Dynamics Filter
open scoped Topology

/-- Article: no auxiliary returns for Polyak's explicit τ=0. -/
theorem response_polyak_abs_lt {q : ℝ} (hq : 0<q) (hq1 : q<1) (k : ℕ) (hk : 1 ≤ k) :
    |response 0 (q^2) k|<1 := by
  have hq2 : q^2<1 := by nlinarith
  have hdiv := Nat.mod_add_div k 2
  rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
  · have he : k=2*(k/2) := by omega
    rw [he,(response_polyak_even q (k/2)).1,abs_pow,abs_neg,abs_of_nonneg (sq_nonneg q)]
    exact pow_lt_one₀ (sq_nonneg q) hq2 (by omega)
  · have he : k=2*(k/2)+1 := by omega
    rw [he,(response_polyak_even q (k/2)).2,abs_pow,abs_neg,abs_of_nonneg (sq_nonneg q)]
    exact pow_lt_one₀ (sq_nonneg q) hq2 (by omega)

variable {J : Type*} [Fintype J]

/-- Article: explicit Polyak startup model in r complex coordinates and one scalar coordinate.
Use: the scalar part is exactly Y(-q²)ⁿ at time 2n and Y(-q²)ⁿ⁺¹ at time 2n+1. -/
theorem exists_polyak_startup_model {μ L C t : ℝ} (hμ : 0<μ) (hL : μ<L)
    (w : J → NNReal) (c : J → Frequency) (hw : ∑ j,w j=1)
    (h : Feasible (t-Real.log (polyakQ μ L)) t (finiteSpectrum w c hw) C)
    (hstrict : 0<t → |C|<meanG (finiteSpectrum w c hw) (Real.sinh (t-Real.log (polyakQ μ L)))) :
    ∃ Y : ℝ, ∃ ψ : WithLp 2 (EuclideanSpace ℂ J × ℝ) → ℝ,
      0<Y ∧ NormalizedSmooth ψ ∧ ∀ N : ℕ,
      iterate (gradient (denormalizeFunction μ L ψ)) (polyakAlpha μ L) (polyakBeta μ L)
        (startupPosition (finitePosition w c t) 0 (2*polyakQ μ L) (polyakQ μ L^2) 0 Y (some 0)) N=
      startupPosition (finitePosition w c t) 0 (2*polyakQ μ L) (polyakQ μ L^2) 0 Y (some N) := by
  let q := polyakQ μ L
  have hq : 0<q := polyakQ_pos hμ hL
  have hq1 : q<1 := polyakQ_lt_one hμ hL
  let m := multiplierMap 0 (2*q) (q^2) t
  let x := finitePosition w c t
  let σ := finiteGradient w c m t
  let v := finiteValue w c m C t
  have hfeas : MixtureFeasible (finiteSpectrum w c hw) m C t := by
    rwa [show m=polyakMultiplier (t-Real.log q) from multiplierMap_polyak q t hq,
      mixtureFeasible_polyak_iff]
  have hstr : 0<t → |C|<spectrumG (finiteSpectrum w c hw) m := by
    intro ht
    simpa only [m,multiplierMap_polyak q t hq,spectrumG_polyak] using hstrict ht
  have hno : ∀ k,1 ≤ k → response (0+2*q*0) (q^2) k≠1 := by
    intro k hk he
    have hh := response_polyak_abs_lt hq hq1 k hk
    simp only [mul_zero,zero_add] at he
    rw [he,abs_one] at hh
    exact (lt_irrefl 1) hh
  have hlim : Tendsto (response (0+2*q*0) (q^2)) atTop (𝓝 0) := by
    apply response_tendsto_zero (sq_nonneg q) (by nlinarith)
    simp only [mul_zero,zero_add,abs_zero]
    positivity
  obtain ⟨Y,ψ,hY,hψ,hdata⟩ := exists_startup_potential_fixed (A := 0) (B := 2*q)
    (β := q^2) (τ := 0) (by norm_num) hno hlim x σ v
    (finite_tableFeasible w c hw hfeas) (finitePosition_none w c t)
    (finiteGradient_none w c m t) (finiteValue_none w c m C t)
    (finite_startup_control w c hw hstr) (initialGradient x 0 (2*q) (q^2))
  refine ⟨Y,ψ,hY,hψ,fun N => ?_⟩
  have hrec := finite_recurrence w c 0 (2*q) (q^2) t (by positivity)
  have hAn : normalizedA μ L (polyakAlpha μ L) (polyakQ μ L^2)=0 := by
    simpa only [polyakBeta] using polyak_normalizedA hμ hL
  have hBn := polyak_normalizedB hμ hL
  have hh := startup_iterate (μ := μ) (L := L) (α := polyakAlpha μ L) (β := polyakBeta μ L)
    (τ := 0) (Y := Y) x σ hψ
    (by rw [polyak_normalizedB hμ hL]; positivity)
    (by simpa only [hAn,hBn,polyakBeta] using
      fun i => (hdata i).2)
    (by simpa only [hAn,hBn,polyakBeta] using hrec) N
  simpa only [hAn,hBn,polyakBeta] using hh

omit [Fintype J] in
/-- Article: the actual added Polyak coordinate, at even and odd times. -/
theorem startup_polyak_scalar (x : Option ℕ → EuclideanSpace ℂ J) (q Y : ℝ) (n : ℕ) :
    (startupPosition x 0 (2*q) (q^2) 0 Y (some (2*n))).snd=Y*(-q^2)^n ∧
    (startupPosition x 0 (2*q) (q^2) 0 Y (some (2*n+1))).snd=Y*(-q^2)^(n+1) := by
  simp only [startupPosition,productPosition,scalarPosition,mul_zero,zero_add,WithLp.toLp_snd]
  change Y*response 0 (q^2) (2*n)=Y*(-q^2)^n ∧ Y*response 0 (q^2) (2*n+1)=Y*(-q^2)^(n+1)
  exact And.intro (congrArg (fun z => Y*z) (response_polyak_even q n).1)
      (congrArg (fun z => Y*z) (response_polyak_even q n).2)

end
end polyak.Realization
