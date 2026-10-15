import «2610.05164v2».Filters.GroundComparison
import «2610.05164v2».Continuum.KernelSquareIntegral

/-!
Article: 2610.05164v2, Theorem 5.1.
The general linear-filter square identity in Proposition 3(i).
Use: `«2610.05164v2».Filters.linear_square_trace` feeds
`«2610.05164v2».DualCertificate.NormalizedCalibration.S_actual` (S actual).
Proof chain: `«2610.05164v2».Primal.square_trace_cubic` — 2610.05164v2, Theorem 5.1; General
measurable speed gives a density with the prescribed ground parameter.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Continuum «2610.05164v2».GroundState
set_option backward.isDefEq.respectTransparency false

/--
Measurability of the displayed map: `Measurable (fun p : ℝ × ℝ => kernel c p.1 p.2)`.

Use: `«2610.05164v2».Filters.causal_square_integral` uses this measurability result to
establish exact identity `(∫ x, (causal 2 m x)^2)=(1/4:ℝ)*∫ y, ∫ z, exp (-2*|y-z|)*m y*m z`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.relaxed_energy_ge_value`.

Proof: Separate `p.2 ≤ p.1` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem kernel_joint_measurable (c : ℝ) : Measurable (fun p : ℝ × ℝ => kernel c p.1 p.2) := by
  have he : (fun p : ℝ × ℝ => kernel c p.1 p.2)=
      {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (fun p => exp (-c*(p.1-p.2))) := by
    funext p
    by_cases h : p.2 ≤ p.1 <;> simp [kernel,h]
  rw [he]
  exact (by fun_prop : Measurable (fun p : ℝ × ℝ => exp (-c*(p.1-p.2)))).indicator
    (measurableSet_le measurable_snd measurable_fst)

/--
Exact identity `kernel 2 x y*kernel 2 x z = exp (2*y+2*z)*(Ici (max y z)).indicator (fun x =>
exp (-4*x)) x`.

Use: `«2610.05164v2».Filters.kernel_pair_integrable` rewrites with this identity to establish
integrability of the displayed function: `Integrable (fun x => kernel 2 x y*kernel 2 x z)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.relaxed_energy_ge_value`.

Proof: Separate `y ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem kernel_pair_formula (y z x : ℝ) :
    kernel 2 x y*kernel 2 x z =
      exp (2*y+2*z)*(Ici (max y z)).indicator (fun x => exp (-4*x)) x := by
  -- Separate `y ≤ x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hy : y ≤ x <;> by_cases hz : z ≤ x
  · rw [kernel,indicator_of_mem (show y ∈ Iic x from hy),
      indicator_of_mem (show z ∈ Iic x from hz),
      indicator_of_mem (show x ∈ Ici (max y z) from max_le hy hz),← exp_add,← exp_add]
    congr 1
    ring
  · simp [kernel,hy,hz,show ¬max y z ≤ x from fun h => hz ((le_max_right _ _).trans h)]
  · simp [kernel,hy,hz,show ¬max y z ≤ x from fun h => hy ((le_max_left _ _).trans h)]
  · simp [kernel,hy,hz,show ¬max y z ≤ x from fun h => hy ((le_max_left _ _).trans h)]

/--
Integrability of the displayed function: `Integrable (fun x => kernel 2 x y*kernel 2 x z)`.

Use: a standalone supporting integrability result for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 5.1.

Proof: Use the identities/estimates `«2610.05164v2».Filters.kernel_pair_formula` with the
arguments shown in the proof.
-/
theorem kernel_pair_integrable (y z : ℝ) : Integrable (fun x => kernel 2 x y*kernel 2 x z) := by
  simp_rw [kernel_pair_formula]
  apply Integrable.const_mul
  apply IntegrableOn.integrable_indicator _ measurableSet_Ici
  apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
  exact integrableOn_exp_mul_Ioi (by norm_num : (-4:ℝ) < 0) _

/--
Exact identity `(∫ x, kernel 2 x y*kernel 2 x z)=exp (-2*|y-z|)/4`.

Use: `«2610.05164v2».Filters.causal_square_integral` rewrites with this identity to establish
exact identity `(∫ x, (causal 2 m x)^2)=(1/4:ℝ)*∫ y, ∫ z, exp (-2*|y-z|)*m y*m z`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.relaxed_energy_ge_value`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.kernel_pair_formula` with the
arguments shown in the proof.
-/
theorem kernel_pair_mass (y z : ℝ) : (∫ x, kernel 2 x y*kernel 2 x z)=exp (-2*|y-z|)/4 := by
  -- Use the identities/estimates `«2610.05164v2».Filters.kernel_pair_formula` with the
  -- arguments shown in the proof.
  simp_rw [kernel_pair_formula]
  rw [integral_const_mul,integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (by norm_num : (-4:ℝ) < 0)]
  have he : 2*y+2*z+-4*max y z = -2*|y-z| := by
    rcases le_total y z with h | h
    · rw [max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  rw [div_neg,neg_div,neg_neg,← mul_div_assoc,← exp_add,he]

/--
Integrability of the displayed function: `Integrable (fun x => (causal 2 m x)^2)`.

Use: `«2610.05164v2».Filters.causal_square_integral` uses this integrability result to
establish exact identity `(∫ x, (causal 2 m x)^2)=(1/4:ℝ)*∫ y, ∫ z, exp (-2*|y-z|)*m y*m z`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.square_trace_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_integrable`,
`«2610.05164v2».Filters.causal_continuous`, `«2610.05164v2».Filters.causal_nonneg` with the
arguments shown in the proof.
-/
theorem causal_square_integrable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) :
    Integrable (fun x => (causal 2 m x)^2) := by
  -- Use the identities/estimates `«2610.05164v2».Filters.causal_integrable`,
  -- `«2610.05164v2».Filters.causal_continuous`, `«2610.05164v2».Filters.causal_nonneg` with
  -- the arguments shown in the proof.
  have hi := causal_integrable (by norm_num : (0:ℝ) < 2) hm
  apply (hi.norm.mul_const (∫ t, m t)).mono'
  · exact (causal_continuous (by norm_num : (0:ℝ) ≤ 2) hm).pow 2 |>.aestronglyMeasurable
  · exact Eventually.of_forall (fun x => by
      have h0 := causal_nonneg (c := 2) (Eventually.of_forall hn) x
      have h1 := causal_le_mass (by norm_num : (0:ℝ) ≤ 2) hm (Eventually.of_forall hn) x
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs,abs_of_nonneg h0]
      nlinarith)

/--
The general linear-filter square identity in Proposition 3(i).

Exact identity `(∫ x, (causal 2 m x)^2)=(1/4:ℝ)*∫ y, ∫ z, exp (-2*|y-z|)*m y*m z`.

Use: `«2610.05164v2».Filters.linear_square_trace` rewrites with this identity to establish
exact identity `(∫ x, (linear hm hn x)^2)=groundParameter hm hn^2/4*(∑' j, kernelEigenvalue hm
hn j^2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.relaxed_energy_ge_value`.

Proof: Expand the square of the causal integral as a product integral in y and z. Prove joint
measurability and integrability of the resulting three-variable integrand; nonnegativity
identifies its norm integral with the already integrable causal square. Fubini then permits
integration in x first, where the explicit kernel-pair mass is exp(-2|y-z|)/4.
-/
theorem causal_square_integral {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) :
    (∫ x, (causal 2 m x)^2)=(1/4:ℝ)*∫ y, ∫ z, exp (-2*|y-z|)*m y*m z := by
  -- Keep both copies of the causal kernel in one product integrand; this avoids exchanging
  -- integrals before the hypotheses have been checked.
  let F : ℝ → ℝ × ℝ → ℝ := fun x p => (kernel 2 x p.1*m p.1)*(kernel 2 x p.2*m p.2)
  -- Establish hFi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hFi (x : ℝ) : Integrable (F x) (volume.prod volume) :=
    (kernel_mul_integrable (by norm_num : (0:ℝ) ≤ 2) hm x).mul_prod
      (kernel_mul_integrable (by norm_num : (0:ℝ) ≤ 2) hm x)
  -- At fixed x, the product measure integral is exactly the square of the one-variable causal
  -- integral.
  have hFe (x : ℝ) : (∫ p, F x p ∂volume.prod volume)=(causal 2 m x)^2 := by
    change (∫ p : ℝ × ℝ, (kernel 2 x p.1*m p.1)*(kernel 2 x p.2*m p.2) ∂volume.prod volume)=_
    rw [integral_prod_mul (fun t => kernel 2 x t*m t) (fun t => kernel 2 x t*m t),← causal_integral]
    ring
  have hFm : AEStronglyMeasurable (Function.uncurry F) (volume.prod (volume.prod volume)) := by
    have h₁ : Measurable (fun p : ℝ × (ℝ × ℝ) => kernel 2 p.1 p.2.1) :=
      (kernel_joint_measurable 2).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h₂ : Measurable (fun p : ℝ × (ℝ × ℝ) => kernel 2 p.1 p.2.2) :=
      (kernel_joint_measurable 2).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    exact (h₁.aestronglyMeasurable.mul hm.aestronglyMeasurable.comp_fst.comp_snd).mul
      (h₂.aestronglyMeasurable.mul hm.aestronglyMeasurable.comp_snd.comp_snd)
  -- Joint integrability is the actual Fubini premise. Nonnegativity reduces the
  -- norm-integrability obligation to causal_square_integrable.
  have hF : Integrable (Function.uncurry F) (volume.prod (volume.prod volume)) := by
    apply (integrable_prod_iff hFm).mpr
    refine ⟨Eventually.of_forall hFi,?_⟩
    have he : (fun x => ∫ p, ‖F x p‖ ∂volume.prod volume)=fun x => (causal 2 m x)^2 := by
      funext x
      rw [← hFe x]
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        apply Real.norm_of_nonneg
        exact mul_nonneg (mul_nonneg (kernel_nonneg _ _ _) (hn _))
          (mul_nonneg (kernel_nonneg _ _ _) (hn _)))
    change Integrable (fun x : ℝ => ∫ p : ℝ × ℝ, ‖F x p‖ ∂volume.prod volume)
    rw [he]
    exact causal_square_integrable hm hn
  -- Now exchange integration order and evaluate the x integral by the explicit
  -- kernel_pair_mass formula.
  calc
    _ = ∫ x : ℝ, (∫ p : ℝ × ℝ, F x p ∂volume.prod volume) := by simp_rw [hFe]
    _ = ∫ p : ℝ × ℝ, (∫ x : ℝ, F x p) ∂volume.prod volume := integral_integral_swap hF
    _ = ∫ p : ℝ × ℝ, exp (-2*|p.1-p.2|)/4*(m p.1*m p.2) ∂volume.prod volume := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        have he : (fun x => F x p) = fun x => (kernel 2 x p.1*kernel 2 x p.2)*(m p.1*m p.2) := by
          funext x
          dsimp [F]
          ring
        change (∫ x : ℝ, F x p)=_
        rw [he,integral_mul_const,kernel_pair_mass])
    _ = (1/4:ℝ)*∫ y, ∫ z, exp (-2*|y-z|)*m y*m z := by
      rw [← integral_const_mul]
      have hi := hF.integral_prod_right
      have he : (fun p : ℝ × ℝ => ∫ x, F x p)=
          fun p => exp (-2*|p.1-p.2|)/4*(m p.1*m p.2) := by
        funext p
        have he' : (fun x => F x p)=fun x => (kernel 2 x p.1*kernel 2 x p.2)*(m p.1*m p.2) := by
          funext x
          dsimp [F]
          ring
        rw [he',integral_mul_const,kernel_pair_mass]
      change Integrable (fun p : ℝ × ℝ => ∫ x : ℝ, F x p) (volume.prod volume) at hi
      rw [he] at hi
      rw [integral_prod _ hi]
      congr 1
      funext y
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by ring)

/--
Exact identity `(∫ x, (linear hm hn x)^2)=groundParameter hm hn^2/4*(∑' j, kernelEigenvalue hm
hn j^2)`.

Use: `«2610.05164v2».Comparison.symmetric_square_trace` rewrites with this identity to
establish the precise assertion is `(groundParameter hm hn)^2/4*(∑' j, kernelEigenvalue hm hn
j^2)= 2*(∫ x in Iic (0:ℝ), (linear hm hn x)^2)+(linear hm hn 0)^2`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.relaxed_energy_ge_value`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem linear_square_trace {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) :
    (∫ x, (linear hm hn x)^2)=groundParameter hm hn^2/4*(∑' j, kernelEigenvalue hm hn j^2) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  simp only [linear,mul_pow]
  rw [integral_const_mul,causal_square_integral hm hn,kernelEigenvalue_square_integral hm hn]
  have he : (∫ y : ℝ, ∫ z : ℝ, exp (-2*|y-z|)*m y*m z)=
      ∫ y : ℝ, ∫ z : ℝ, m y*m z*exp (-2*|y-z|) := by
    congr 1
    funext y
    congr 1
    funext z
    ring
  rw [he]
  ring

end
end «2610.05164v2».Filters
