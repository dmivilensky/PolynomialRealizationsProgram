import «2610.05164v2».Continuum.NuclearNorm

/-!
Article: 2610.05164v2, Lemma 4.
Nuclear Algebra.
Use: `«2610.05164v2».Continuum.nuclearNorm_toReal_eq_zero_iff` feeds
`«2610.05164v2».Continuum.TraceClassOperator.normCore` (norm Core).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus. The
needed form is proved here.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
The stated quantitative bound `0 ≤ C`.

Use: `«2610.05164v2».Continuum.TraceBound.opNorm_le` uses this bound to establish the stated
quantitative bound `‖T‖ ≤ C`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem TraceBound.nonneg {T : E →L[ℝ] E} {C : ℝ} (h : TraceBound T C) : 0 ≤ C := by
  have hz : Orthonormal ℝ (fun _ : Fin 0 => (0 : E)) := Orthonormal.of_isEmpty _
  simpa using h 0 _ _ hz hz

/--
The stated quantitative bound `‖T‖ ≤ C`.

Use: `«2610.05164v2».Continuum.nuclearNorm_toReal_eq_zero_iff` uses this bound to establish
equivalence of the displayed criteria: `(nuclearNorm T).toReal = 0 ↔ T = 0`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Separate `T x = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
theorem TraceBound.opNorm_le {T : E →L[ℝ] E} {C : ℝ} (h : TraceBound T C) : ‖T‖ ≤ C := by
  -- Separate `T x = 0` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  apply ContinuousLinearMap.opNorm_le_of_unit_norm h.nonneg
  intro x hx
  by_cases hz : T x = 0
  · simpa only [hz, norm_zero] using h.nonneg
  have hn : ‖T x‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hu : ‖‖T x‖⁻¹ • T x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hn]
  have huf : Orthonormal ℝ (fun _ : Fin 1 => ‖T x‖⁻¹ • T x) :=
    orthonormal_subsingleton_iff.mpr (fun _ => hu)
  have hxf : Orthonormal ℝ (fun _ : Fin 1 => x) := orthonormal_subsingleton_iff.mpr (fun _ => hx)
  have hb := h 1 _ _ huf hxf
  have he : inner ℝ (‖T x‖⁻¹ • T x) (T x) = ‖T x‖ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  simpa only [Fin.sum_univ_one, he, abs_of_nonneg (norm_nonneg _)] using hb

/--
The precise assertion is `TraceBound T (nuclearNorm T).toReal`.

Use: `«2610.05164v2».Continuum.IsTraceClass.add` uses this assertion to establish the
trace-class property: `IsTraceClass (S+T)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.traceBound_of_nuclearNorm_le`
with the arguments shown in the proof.
-/
theorem IsTraceClass.traceBound {T : E →L[ℝ] E} (h : IsTraceClass T) :
    TraceBound T (nuclearNorm T).toReal := by
  apply traceBound_of_nuclearNorm_le ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal (ne_of_lt h)]

/--
Exact identity `nuclearNorm (0 : E →L[ℝ] E) = 0`.

Use: `«2610.05164v2».Continuum.IsTraceClass.zero` rewrites with this identity to establish the
trace-class property: `IsTraceClass (0 : E →L[ℝ] E)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.nuclearNorm_le_of_traceBound`
with the arguments shown in the proof.
-/
theorem nuclearNorm_zero : nuclearNorm (0 : E →L[ℝ] E) = 0 := by
  apply le_antisymm _ bot_le
  apply (nuclearNorm_le_of_traceBound (C := 0) ?_).trans_eq (by simp)
  intro n u v hu hv
  simp

/--
The trace-class property: `IsTraceClass (0 : E →L[ℝ] E)`.

Use: `«2610.05164v2».Continuum.traceClassSubmodule` uses this assertion in the displayed
construction of `traceClassSubmodule`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.nuclearNorm_zero` with the
arguments shown in the proof.
-/
theorem IsTraceClass.zero : IsTraceClass (0 : E →L[ℝ] E) := by
  unfold IsTraceClass
  rw [nuclearNorm_zero]
  exact ENNReal.zero_lt_top

/--
The trace-class property: `IsTraceClass (S+T)`.

Use: `«2610.05164v2».Continuum.IsTraceClass.sub` uses this assertion to establish the
trace-class property: `IsTraceClass (S-T)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.TraceBound.isTraceClass`,
`«2610.05164v2».Continuum.TraceBound.add`, `«2610.05164v2».Continuum.IsTraceClass.traceBound`
with the arguments shown in the proof.
-/
theorem IsTraceClass.add {S T : E →L[ℝ] E} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S+T) := (hS.traceBound.add hT.traceBound).isTraceClass

/--
The trace-class property: `IsTraceClass (c • T)`.

Use: `«2610.05164v2».Continuum.IsTraceClass.neg` uses this assertion to establish the
trace-class property: `IsTraceClass (-T)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.TraceBound.isTraceClass`,
`«2610.05164v2».Continuum.TraceBound.smul`, `«2610.05164v2».Continuum.IsTraceClass.traceBound`
with the arguments shown in the proof.
-/
theorem IsTraceClass.smul {T : E →L[ℝ] E} (hT : IsTraceClass T) (c : ℝ) :
    IsTraceClass (c • T) := (hT.traceBound.smul c).isTraceClass

/--
The trace-class property: `IsTraceClass (-T)`.

Use: `«2610.05164v2».Continuum.IsTraceClass.sub` uses this assertion to establish the
trace-class property: `IsTraceClass (S-T)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.IsTraceClass.smul` with the
arguments shown in the proof.
-/
theorem IsTraceClass.neg {T : E →L[ℝ] E} (hT : IsTraceClass T) : IsTraceClass (-T) := by simpa only [neg_one_smul] using hT.smul (-1)

/--
The trace-class property: `IsTraceClass (S-T)`.

Use: `«2610.05164v2».HalfLine.operator_traceClass` uses this assertion to establish the
trace-class property: `IsTraceClass (operator hm hn x)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.IsTraceClass.add`,
`«2610.05164v2».Continuum.IsTraceClass.neg` with the arguments shown in the proof.
-/
theorem IsTraceClass.sub {S T : E →L[ℝ] E} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S-T) := by simpa only [sub_eq_add_neg] using hS.add hT.neg

/--
The stated quantitative bound `(nuclearNorm T).toReal ≤ C`.

Use: `«2610.05164v2».Continuum.nuclearNorm_toReal_add_le` uses this bound to establish the
stated quantitative bound `(nuclearNorm (S+T)).toReal ≤ (nuclearNorm S).toReal + (nuclearNorm
T).toReal`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.nuclearNorm_le_of_traceBound`,
`«2610.05164v2».Continuum.TraceBound.nonneg` with the arguments shown in the proof.
-/
theorem nuclearNorm_toReal_le {T : E →L[ℝ] E} {C : ℝ} (h : TraceBound T C) :
    (nuclearNorm T).toReal ≤ C := by
  have hn := nuclearNorm_le_of_traceBound h
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hn).trans_eq (ENNReal.toReal_ofReal h.nonneg)

/--
The stated quantitative bound `(nuclearNorm (S+T)).toReal ≤ (nuclearNorm S).toReal +
(nuclearNorm T).toReal`.

Use: `«2610.05164v2».Continuum.TraceClassOperator.normCore` uses this bound to establish the
precise assertion is `NormedSpace.Core ℝ (TraceClassOperator E) where norm_nonneg _`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.nuclearNorm_toReal_le`,
`«2610.05164v2».Continuum.TraceBound.add`, `«2610.05164v2».Continuum.IsTraceClass.traceBound`
with the arguments shown in the proof.
-/
theorem nuclearNorm_toReal_add_le {S T : E →L[ℝ] E} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    (nuclearNorm (S+T)).toReal ≤ (nuclearNorm S).toReal + (nuclearNorm T).toReal :=
  nuclearNorm_toReal_le (hS.traceBound.add hT.traceBound)

/--
Exact identity `(nuclearNorm (c • T)).toReal = |c| * (nuclearNorm T).toReal`.

Use: `«2610.05164v2».Continuum.TraceClassOperator.normCore` rewrites with this identity to
establish the precise assertion is `NormedSpace.Core ℝ (TraceClassOperator E) where norm_nonneg
_`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Separate `c = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem nuclearNorm_toReal_smul {T : E →L[ℝ] E} (hT : IsTraceClass T) (c : ℝ) :
    (nuclearNorm (c • T)).toReal = |c| * (nuclearNorm T).toReal := by
  -- Separate `c = 0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  apply le_antisymm (nuclearNorm_toReal_le (hT.traceBound.smul c))
  by_cases hc : c = 0
  · simp [hc]
  have h := nuclearNorm_toReal_le ((hT.smul c).traceBound.smul c⁻¹)
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul, abs_inv] at h
  have ha : 0 < |c| := abs_pos.mpr hc
  have := mul_le_mul_of_nonneg_left h ha.le
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt ha), one_mul] using this

/--
Equivalence of the displayed criteria: `(nuclearNorm T).toReal = 0 ↔ T = 0`.

Use: `«2610.05164v2».Continuum.TraceClassOperator.normCore` rewrites with this identity to
establish the precise assertion is `NormedSpace.Core ℝ (TraceClassOperator E) where norm_nonneg
_`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.TraceBound.opNorm_le`,
`«2610.05164v2».Continuum.IsTraceClass.traceBound`, `«2610.05164v2».Continuum.nuclearNorm_zero`
with the arguments shown in the proof.
-/
theorem nuclearNorm_toReal_eq_zero_iff {T : E →L[ℝ] E} (hT : IsTraceClass T) :
    (nuclearNorm T).toReal = 0 ↔ T = 0 := by
  constructor
  · intro h
    exact norm_eq_zero.mp (le_antisymm (h ▸ hT.traceBound.opNorm_le) (norm_nonneg _))
  · intro h
    simp [h, nuclearNorm_zero]

end
end «2610.05164v2».Continuum
