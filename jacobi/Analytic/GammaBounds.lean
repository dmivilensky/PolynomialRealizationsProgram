import jacobi.Analytic.ReferenceNorming
import jacobi.Analysis.UniformGammaRatio

/-!
Article: jacobi, Lemma C.1.
Complex Gamma norms are compared with their positive real-part Gamma
values using the actual Euler integral and exact recurrence. Together
with the proved uniform real Gamma-ratio bound, this controls the
reference norm scale without a uniform Stirling assumption.
Use: bounds the actual complex reference norm denominator uniformly by the real Gamma scale.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual complex Gamma norm is bounded above by Gamma at its positive real part.
Use: bounds the actual complex reference norm denominator uniformly by the real Gamma scale.
Article: jacobi, Lemma C.1.
Source: Euler's convergent Gamma integral, mathlib Gamma.Basic.
Proof: take the norm inside the genuine Euler integral. On the positive
axis the complex power norm is exactly the corresponding real-part
power, so the resulting integral is the actual real Gamma function. -/
theorem gamma_norm_le_real {s : ℂ} (hs : 0<s.re) : ‖Complex.Gamma s‖≤Real.Gamma s.re := by
  -- This compares the original Gamma functions, without an asymptotic majorant premise.
  rw [Complex.Gamma_eq_integral hs,Complex.GammaIntegral,Real.Gamma_eq_integral hs]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.sub_re,Complex.one_re]

/-- Shifting a positive-real-part Gamma argument preserves a strictly positive multiple of its real-part Gamma scale.
Use: supplies the lower complex Gamma norm bound in the original reference norm estimate.
Article: jacobi, Lemma C.1.
Proof: at zero shift the bound is equality. At each genuine Gamma
recurrence step the norm of s+n is at least Re(s)+n, so the same positive
initial quotient remains a valid lower coefficient at every index. -/
theorem gamma_norm_shift_lower {s : ℂ} (hs : 0<s.re) (n : ℕ) :
    (‖Complex.Gamma s‖/Real.Gamma s.re)*Real.Gamma ((n:ℝ)+s.re)≤‖Complex.Gamma ((n:ℂ)+s)‖ := by
  -- The only coefficient is the actual initial Gamma quotient; no unproved uniform limit is used.
  let m : ℝ := ‖Complex.Gamma s‖/Real.Gamma s.re
  have hm : 0≤m := div_nonneg (norm_nonneg _) (Real.Gamma_pos_of_pos hs).le
  change m*Real.Gamma ((n:ℝ)+s.re)≤_
  induction n with
  | zero => simp [m,(Real.Gamma_pos_of_pos hs).ne']
  | succ n ih =>
    have hr : 0<(n:ℝ)+s.re := by positivity
    have hc : 0<((n:ℂ)+s).re := by simpa only [Complex.add_re,Complex.natCast_re] using hr
    have hsn : (n+1:ℂ)+s=((n:ℂ)+s)+1 := by ring
    have hsr : (n+1:ℝ)+s.re=((n:ℝ)+s.re)+1 := by ring
    simp only [Nat.cast_add,Nat.cast_one]
    rw [hsn,hsr,Complex.Gamma_add_one _ (ne_of_apply_ne Complex.re hc.ne'),
      Real.Gamma_add_one hr.ne',norm_mul]
    calc
      _ = ((n:ℝ)+s.re)*(m*Real.Gamma ((n:ℝ)+s.re)) := by ring
      _ ≤ ‖(n:ℂ)+s‖*‖Complex.Gamma ((n:ℂ)+s)‖ :=
        mul_le_mul (by simpa only [Complex.add_re,Complex.natCast_re] using Complex.re_le_norm ((n:ℂ)+s))
          ih (mul_nonneg hm (Real.Gamma_pos_of_pos hr).le) (norm_nonneg _)

/-- On every compact positive-real-part Gamma parameter set, the normalized complex Gamma ratio has two genuine positive uniform tail bounds.
Use: supplies the full moving-complex-order reference norm scale in analytic GL.
Article: jacobi, Lemma C.1.
Proof: the actual initial Gamma quotient is continuous and positive on
the compact parameter set, hence has a positive minimum. The two
preceding actual Gamma norm comparisons sandwich each complex ratio
between the corresponding real ratio and that ratio divided by the
minimum. Apply the proved uniform Bohr--Mollerup real tail estimate. -/
theorem gamma_ratio_compact_tail {K : Set ℂ} (hK : IsCompact K) (hpos : ∀ s∈K,0<s.re) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ s∈K,∀ n : ℕ,2≤n →
      c≤Real.Gamma ((n:ℝ)+1)/‖Complex.Gamma ((n:ℂ)+s)‖*(n+1:ℝ)^(s.re-1) ∧
      Real.Gamma ((n:ℝ)+1)/‖Complex.Gamma ((n:ℂ)+s)‖*(n+1:ℝ)^(s.re-1)≤C := by
  -- Compactness is used only for an actual nonzero coefficient at zero shift, not for an infinite spectral family.
  by_cases hne : K.Nonempty
  · let q : ℂ → ℝ := fun s => ‖Complex.Gamma s‖/‖Complex.Gamma (s.re:ℂ)‖
    have hq (s : ℂ) (hs : s∈K) : ContinuousWithinAt q K s := by
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.div (gamma_analytic (hpos s hs)).continuousAt.norm
      · have hp : 0<((s.re:ℝ):ℂ).re := hpos s hs
        exact ((gamma_analytic hp).continuousAt.comp_of_eq
          (Complex.continuous_ofReal.continuousAt.comp Complex.continuous_re.continuousAt) rfl).norm
      · exact norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero
          (gamma_no_pole (by simpa only [Complex.ofReal_re] using hpos s hs)))
    have hqe (s : ℂ) (hs : s∈K) : q s=‖Complex.Gamma s‖/Real.Gamma s.re := by
      dsimp only [q]
      rw [Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.Gamma_pos_of_pos (hpos s hs))]
    have hqp (s : ℂ) (hs : s∈K) : 0<q s := by
      rw [hqe s hs]
      exact div_pos (norm_pos_iff.mpr (Complex.Gamma_ne_zero (gamma_no_pole (hpos s hs))))
        (Real.Gamma_pos_of_pos (hpos s hs))
    obtain ⟨s0,hs0,hmin⟩ := hK.exists_isMinOn hne hq
    obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (f := fun s : ℂ => s) continuousOn_id
    let S : ℝ := |B|+1
    have hS : 0<S := by dsimp [S]; positivity
    obtain ⟨H,hH,hreal⟩ := jacobi.Analysis.real_gamma_ratio_tail_bound hS
    refine ⟨Real.exp (-H),Real.exp H/q s0,Real.exp_pos _,div_pos (Real.exp_pos _) (hqp s0 hs0),?_⟩
    intro s hs n hn
    have hsr : s.re≤S := (Complex.re_le_norm s).trans ((hB s hs).trans (by dsimp [S]; linarith [le_abs_self B]))
    obtain ⟨hlo,hup⟩ := hreal s.re (hpos s hs) hsr n hn
    have hr : 0<(n:ℝ)+s.re := by have hp := hpos s hs; positivity
    have hcp : 0<‖Complex.Gamma ((n:ℂ)+s)‖ := norm_pos_iff.mpr
      (Complex.Gamma_ne_zero (gamma_no_pole (by simpa only [Complex.add_re,Complex.natCast_re] using hr)))
    have hgR := Real.Gamma_pos_of_pos hr
    have hgN : 0<Real.Gamma ((n:ℝ)+1) := Real.Gamma_pos_of_pos (by positivity)
    have hpow : 0<(n+1:ℝ)^(s.re-1) := Real.rpow_pos_of_pos (by positivity) _
    have hupper : ‖Complex.Gamma ((n:ℂ)+s)‖≤Real.Gamma ((n:ℝ)+s.re) := by
      simpa only [Complex.add_re,Complex.natCast_re] using gamma_norm_le_real (s := (n:ℂ)+s)
        (by simpa only [Complex.add_re,Complex.natCast_re] using hr)
    have hlower : q s0*Real.Gamma ((n:ℝ)+s.re)≤‖Complex.Gamma ((n:ℂ)+s)‖ := by
      have hh := mul_le_mul_of_nonneg_right (hmin hs) hgR.le
      rw [hqe s hs] at hh
      exact hh.trans (gamma_norm_shift_lower (hpos s hs) n)
    constructor
    · exact hlo.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hgN.le hcp hupper) hpow.le)
    · have hh := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left hgN.le (mul_pos (hqp s0 hs0) hgR) hlower) hpow.le
      apply hh.trans
      calc
        _ = (Real.Gamma ((n:ℝ)+1)/Real.Gamma ((n:ℝ)+s.re)*(n+1:ℝ)^(s.re-1))/q s0 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hup (hqp s0 hs0).le
  · exact ⟨1,1,by norm_num,by norm_num,fun s hs => False.elim (hne ⟨s,hs⟩)⟩

end
end jacobi.ComplexReference
