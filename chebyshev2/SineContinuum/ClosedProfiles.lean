import chebyshev2.SineContinuum.RealLineCoordinate
import Mathlib.Topology.Order.ExtendFrom

/-!
Article: chebyshev2, Proposition 2.
The literal continuous kernel on the full closed square in Lemma 5.
Use: `chebyshev2.SineContinuum.phi_continuousOn` feeds
`chebyshev2.SineContinuum.n_continuous` (n continuous).
Proof chain: `chebyshev2.LocalObstruction.sine_green_scale_tail` — chebyshev2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Set Real MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `l 0=0`.

Use: `chebyshev2.SineContinuum.l_continuousOn` uses this identity to establish continuity
on the stated domain: `ContinuousOn l (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem l_zero : l 0=0 := by simp [l,chebyshev1.SineJacobi.sineProfile]
/--
Exact identity `l 1=0`.

Use: `chebyshev2.SineContinuum.l_continuousOn` uses this identity to establish continuity
on the stated domain: `ContinuousOn l (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.green_mercer_diagonal_uniform`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem l_one : l 1=0 := by simp [l,chebyshev1.SineJacobi.sineProfile]
/--
Exact identity `r 0=0`.

Use: `chebyshev2.SineContinuum.r_continuousOn` uses this identity to establish continuity
on the stated domain: `ContinuousOn r (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.green_mercer_diagonal_uniform`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.l_one` with the arguments
shown in the proof.
-/
theorem r_zero : r 0=0 := by simpa only [r,sub_zero] using l_one
/--
Exact identity `r 1=0`.

Use: `chebyshev2.SineContinuum.r_continuousOn` uses this identity to establish continuity
on the stated domain: `ContinuousOn r (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.l_zero` with the arguments
shown in the proof.
-/
theorem r_one : r 1=0 := by simpa only [r,sub_self] using l_zero

/--
Continuity on the stated domain: `ContinuousOn f (Icc (0:ℝ) 1)`.

Use: `chebyshev2.SineContinuum.l_continuousOn` uses this continuity result to establish
continuity on the stated domain: `ContinuousOn l (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.green_mercer_diagonal_uniform`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem continuousOn_closed_interval {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo (0:ℝ) 1)) (h0 : f 0=0) (h1 : f 1=0)
    (hl : Filter.Tendsto f (𝓝[>] (0:ℝ)) (𝓝 0))
    (hr : Filter.Tendsto f (𝓝[<] (1:ℝ)) (𝓝 0)) : ContinuousOn f (Icc (0:ℝ) 1) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  apply (continuousOn_Icc_extendFrom_Ioo hf hl hr).congr
  intro x hx
  have hxcl : x ∈ closure (Ioo (0:ℝ) 1) := by rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]; exact hx
  symm
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hx with rfl | rfl | hi
  · rw [h0]
    exact extendFrom_eq hxcl (hl.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self))
  · rw [h1]
    exact extendFrom_eq hxcl (hr.mono_left (nhdsWithin_mono _ Ioo_subset_Iio_self))
  · exact extendFrom_extends hf x hi

/--
Continuity on the stated domain: `ContinuousOn l (Icc (0:ℝ) 1)`.

Use: `chebyshev2.SineContinuum.green_continuousOn` uses this continuity result to establish
continuity on the stated domain: `ContinuousOn (fun z : ℝ × ℝ => green z.1 z.2) (Icc (0:ℝ) 1 ×ˢ
Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.green_mercer_diagonal_uniform`.

Proof: Use the identities/estimates
`_private.chebyshev2.SineContinuum.ClosedProfiles.0.chebyshev2.SineContinuum.continuousOn_closed_interval`,
`chebyshev2.SineContinuum.l_derivative`, `chebyshev2.SineContinuum.l_zero` with the
arguments shown in the proof.
-/
theorem l_continuousOn : ContinuousOn l (Icc (0:ℝ) 1) :=
  continuousOn_closed_interval (fun _ ht => (l_derivative ht).continuousAt.continuousWithinAt)
    l_zero l_one l_left_limit l_right_limit

/--
Continuity on the stated domain: `ContinuousOn r (Icc (0:ℝ) 1)`.

Use: `chebyshev2.SineContinuum.green_continuousOn` uses this continuity result to establish
continuity on the stated domain: `ContinuousOn (fun z : ℝ × ℝ => green z.1 z.2) (Icc (0:ℝ) 1 ×ˢ
Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.green_mercer_diagonal_uniform`.

Proof: Use the identities/estimates
`_private.chebyshev2.SineContinuum.ClosedProfiles.0.chebyshev2.SineContinuum.continuousOn_closed_interval`,
`chebyshev2.SineContinuum.r_derivative`, `chebyshev2.SineContinuum.r_zero` with the
arguments shown in the proof.
-/
theorem r_continuousOn : ContinuousOn r (Icc (0:ℝ) 1) :=
  continuousOn_closed_interval (fun _ ht => (r_derivative ht).continuousAt.continuousWithinAt)
    r_zero r_one r_left_limit r_right_limit

/--
The literal continuous kernel on the full closed square in Lemma 5.

Continuity on the stated domain: `ContinuousOn (fun z : ℝ × ℝ => green z.1 z.2) (Icc (0:ℝ) 1 ×ˢ
Icc (0:ℝ) 1)`.

Use: `chebyshev2.SineContinuum.green_eigenfunction` uses this continuity result to
establish exact identity `(∫ s in (0:ℝ)..1, green t s*upsilon n s)=upsilon n t/mu n`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.green_mercer_diagonal_uniform`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.l_continuousOn`,
`chebyshev2.SineContinuum.r_continuousOn` with the arguments shown in the proof.
-/
theorem green_continuousOn :
    ContinuousOn (fun z : ℝ × ℝ => green z.1 z.2) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
  -- Establish continuity hl before using the function at limits or in calculus arguments.
  have hl : ContinuousOn (fun z : ℝ × ℝ => l (min z.1 z.2))
      (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := l_continuousOn.comp (continuous_fst.min continuous_snd).continuousOn
    (fun _ hz => ⟨le_min hz.1.1 hz.2.1,(min_le_left _ _).trans hz.1.2⟩)
  -- Establish continuity hr before using the function at limits or in calculus arguments.
  have hr : ContinuousOn (fun z : ℝ × ℝ => r (max z.1 z.2))
      (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := r_continuousOn.comp (continuous_fst.max continuous_snd).continuousOn
    (fun _ hz => ⟨hz.1.1.trans (le_max_left _ _),max_le hz.1.2 hz.2.2⟩)
  exact (hl.const_mul (1/2:ℝ)).mul hr

/--
Continuity on the stated domain: `ContinuousOn SineJacobi.phi (Icc (0:ℝ) 1)`.

Use: `chebyshev2.SineContinuum.energy_integrable` uses this continuity result to establish
integrability of the displayed function: `Integrable (fun x => m x*sqrt (m x))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem phi_continuousOn : ContinuousOn SineJacobi.phi (Icc (0:ℝ) 1) := by
  have he : SineJacobi.phi=l*r := by funext t; exact phi_product t
  rw [he]
  exact l_continuousOn.mul r_continuousOn

/--
Exact identity `(∫ t in (0:ℝ)..1, green t t)=1/2`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 2.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem green_diagonal_integral : (∫ t in (0:ℝ)..1, green t t)=1/2 := by
  have he : (fun t => green t t)=(fun t => (1/2)*SineJacobi.phi t) := by
    funext t
    linarith [green_diagonal t]
  rw [he,intervalIntegral.integral_const_mul,SineJacobi.phi_integral,mul_one]

end
end chebyshev2.SineContinuum
