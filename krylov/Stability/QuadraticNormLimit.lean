import krylov.Stability.C1VanishingProduct
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), genuine quadratic-output norm limit.
Use: a proved actual cubic vector remainder determines the true positive
scale-squared output-norm coefficient, including a zero leading vector.
Source: reverse norm triangle inequality and standard genuine little-o
power comparison and quotient filter limits from mathlib.
-/

namespace krylov.Stability
noncomputable section
open Filter Topology Asymptotics
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual norm of a vector output with a genuine quadratic leading
term and cubic remainder has precisely that leading scale-squared limit.
Use: original physical sharpness includes true zero coefficients and does
not assume a normalized output expansion or its desired limiting value.
Article: main_krylov, thm:local(b), actual quadratic norm coefficient.
Proof: the reverse norm triangle inequality transfers the true vector
remainder to its actual scalar norm. Cubic order is little-o of squared
scale, so the real divided remainder tends to zero. Positive scales make
the exact quadratic leading norm quotient its true constant. -/
theorem quadratic_output_norm_tendsto (v : ℝ → E) (a : E)
    (h : (fun t : ℝ => v t+t^2 • a) =O[𝓝 0] (fun t => ‖t‖^3)) :
    Tendsto (fun t : ℝ => ‖v t‖/t^2) (𝓝[>] 0) (𝓝 ‖a‖) := by
  have hn : (fun t : ℝ => ‖v t‖-t^2*‖a‖) =O[𝓝 0] (fun t => ‖t‖^3) := by
    have hnorm : (fun t : ℝ => ‖v t‖-‖-(t^2 • a)‖) =O[𝓝 0] (fun t => v t- -(t^2 • a)) :=
      isBigO_of_le _ (fun t => by simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (v t) (-(t^2 • a)))
    have he : (fun t : ℝ => v t- -(t^2 • a)) =O[𝓝 0] (fun t => ‖t‖^3) := by
      simpa only [sub_neg_eq_add] using h
    apply (hnorm.trans he).congr_left
    intro t
    rw [norm_neg,norm_smul,Real.norm_of_nonneg (sq_nonneg t)]
  have hl : (fun t : ℝ => ‖v t‖-t^2*‖a‖) =o[𝓝 0] (fun t => t^2) := by
    simpa only [Real.norm_eq_abs,sq_abs] using hn.trans_isLittleO
      (isLittleO_norm_pow_norm_pow (by norm_num : 2<3))
  have hq : Tendsto (fun t : ℝ => (‖v t‖-t^2*‖a‖)/t^2+‖a‖) (𝓝[>] 0) (𝓝 ‖a‖) := by
    simpa only [zero_add] using
      (hl.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds).add tendsto_const_nhds
  apply hq.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t≠0 := (show 0<t from ht).ne'
  field_simp
  ring

end
end krylov.Stability
