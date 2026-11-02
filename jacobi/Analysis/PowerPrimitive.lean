import jacobi.Analysis.AsymptoticSlope
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Article: jacobi, Proposition C.4.
Source: the real mean value theorem and differentiation of real powers.
Use: energyGreen_diagonal_limit obtains the original Green diagonal from its genuine Wronskian ratio derivative; packing tails can use the same endpoint primitive lemma.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter
open scoped Topology

/-- Integrating an actual derivative with a divergent power scale gives its exact leading endpoint coefficient.
Use: energyGreen_diagonal_limit obtains the original Green diagonal from its genuine Wronskian ratio derivative; packing tails can use the same endpoint primitive lemma.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Source: Lagrange's mean value theorem in the coordinate x=t^p.
Proof: put q=1/p and differentiate f(x^q). Its derivative tends to q*L, so its quotient by x has that same limit by the proved asymptotic-slope theorem. Substitute the exact inverse power x=t^p on the genuine positive endpoint filter. -/
theorem power_endpoint_limit {f f' : ℝ → ℝ} {p L : ℝ} (hp : p<0)
    (hd : ∀ᶠ t in 𝓝[>] (0:ℝ),HasDerivAt f (f' t) t)
    (hl : Tendsto (fun t : ℝ => t^(1-p)*f' t) (𝓝[>] (0:ℝ)) (𝓝 L)) :
    Tendsto (fun t : ℝ => f t/t^p) (𝓝[>] (0:ℝ)) (𝓝 (L/p)) := by
  -- The change of coordinate turns a divergent endpoint power into the linear coordinate at infinity.
  let q := 1/p
  have hq : q<0 := one_div_neg.mpr hp
  have hp0 : p≠0 := hp.ne
  have ht : Tendsto (fun x : ℝ => x^q) atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hq)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      exact Real.rpow_pos_of_pos hx q
  have hexp : q*(1-p)=q-1 := by dsimp only [q]; field_simp
  have hder : ∀ᶠ x : ℝ in atTop,
      HasDerivAt (fun y : ℝ => f (y^q)) (q*((x^q)^(1-p)*f' (x^q))) x := by
    filter_upwards [ht.eventually hd,eventually_gt_atTop (0:ℝ)] with x hx hxp
    have h := hx.comp x (Real.hasDerivAt_rpow_const (p := q) (Or.inl hxp.ne'))
    convert h using 1
    · rfl
    · rw [← Real.rpow_mul hxp.le,hexp]
      ring
  have hlim := (hl.comp ht).const_mul q
  have hs := asymptotic_slope hder hlim
  have hv : q*L=L/p := by dsimp only [q]; ring
  rw [hv] at hs
  have h := hs.comp (tendsto_rpow_neg_nhdsGT_zero hp)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t htp
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul htp.le,show p*q=1 by dsimp only [q]; field_simp,Real.rpow_one]

end
end jacobi.Analysis
