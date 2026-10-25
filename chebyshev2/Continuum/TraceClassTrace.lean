import chebyshev2.Continuum.TraceClassSpace
import chebyshev2.Continuum.BasisTrace

/-!
Article: chebyshev2, Lemma 4.
The trace is a continuous functional of norm at most one for the nuclear norm, enabling trace to
commute with Bochner integration.
Result: `chebyshev2.Continuum.TraceClassOperator.trace_rankOne` supplies the stated article
conclusion.
Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for trace-class
operators. The needed form is proved here.
-/
namespace chebyshev2.Continuum
noncomputable section
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
Absolute summability of the diagonal of any nuclear operator in every Hilbert basis. Signs are
placed in a second orthonormal frame.

Summability of the displayed sequence: `Summable (fun i => |inner ℝ (b i) (T.val (b i))|) ∧ (∑'
i, |inner ℝ (b i) (T.val (b i))|) ≤ ‖T‖`.

Use: `chebyshev2.Continuum.TraceClassOperator.trace` uses this summability result in the
displayed construction of `trace`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 4 via `chebyshev2.Continuum.TraceClassOperator.trace_rankOne`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Use the identities/estimates `chebyshev2.Continuum.IsTraceClass.traceBound` with the
arguments shown in the proof.
-/
theorem traceClass_diagonal_summable {ι : Type*} (b : HilbertBasis ι ℝ E)
    (T : TraceClassOperator E) :
    Summable (fun i => |inner ℝ (b i) (T.val (b i))|) ∧
      (∑' i, |inner ℝ (b i) (T.val (b i))|) ≤ ‖T‖ := by
  -- Use the identities/estimates `chebyshev2.Continuum.IsTraceClass.traceBound` with the
  -- arguments shown in the proof.
  classical
  let d := fun i => inner ℝ (b i) (T.val (b i))
  have hb (s : Finset ι) : (∑ i ∈ s, |d i|) ≤ ‖T‖ := by
    let e := s.equivFin
    let f : Fin s.card → ι := fun i => (e.symm i : ι)
    have hf : Function.Injective f := fun i j h => e.symm.injective (Subtype.ext h)
    let u : Fin s.card → E := fun i => b (f i)
    let v : Fin s.card → E := fun i => if 0 ≤ d (f i) then u i else -u i
    have hu : Orthonormal ℝ u := b.orthonormal.comp f hf
    have hv : Orthonormal ℝ v := hu.orthonormal_of_forall_eq_or_eq_neg (fun i => by
      dsimp [v]
      split_ifs <;> simp)
    have hi (i : Fin s.card) : inner ℝ (u i) (T.val (v i)) = |d (f i)| := by
      dsimp [v]
      split_ifs with h
      · exact (abs_of_nonneg h).symm
      · simp only [map_neg, inner_neg_right]
        exact (abs_of_neg (lt_of_not_ge h)).symm
    have h := T.property.traceBound s.card u v hu hv
    simp only [hi] at h
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))] at h
    have hr : (∑ i : Fin s.card, |d (f i)|) = ∑ i ∈ s, |d i| := by
      rw [← e.sum_comp (fun i => |d (f i)|)]
      simp only [f, e.symm_apply_apply]
      have hz : s.attach = (Finset.univ : Finset s) := by ext; simp
      simpa only [hz] using s.sum_attach (fun i => |d i|)
    rwa [hr] at h
  exact ⟨summable_of_sum_le (fun _ => abs_nonneg _) hb,
    Real.tsum_le_of_sum_le (fun _ => abs_nonneg _) hb⟩

namespace TraceClassOperator
variable {ι : Type*} (b : HilbertBasis ι ℝ E)

/--
Constructs `traceLinear` of type `TraceClassOperator E →ₗ[ℝ] ℝ` by the displayed record fields.
Data fields specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.Continuum.TraceClassOperator.trace` uses this definition in the displayed
construction of `trace`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 4 via `chebyshev2.Continuum.TraceClassOperator.trace_rankOne`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
def traceLinear : TraceClassOperator E →ₗ[ℝ] ℝ where
  toFun T := ∑' i, inner ℝ (b i) (T.val (b i))
  map_add' S T := by
    simp only [val_add, add_apply, inner_add_right]
    exact (traceClass_diagonal_summable b S).1.of_abs.tsum_add
      (traceClass_diagonal_summable b T).1.of_abs
  map_smul' c T := by
    simp only [val_smul, smul_apply, real_inner_smul_right, RingHom.id_apply, smul_eq_mul]
    exact tsum_mul_left

/--
The trace is a continuous functional of norm at most one for the nuclear norm, enabling trace
to commute with Bochner integration.

Use: `chebyshev2.Continuum.TraceClassOperator.trace_apply` uses this definition to
establish exact identity `trace b T = ∑' i, inner ℝ (b i) (T.val (b i))`.

Article: chebyshev2, Lemma 4 via `chebyshev2.Continuum.TraceClassOperator.trace_rankOne`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.
-/
def trace : TraceClassOperator E →L[ℝ] ℝ := (traceLinear b).mkContinuous 1 (fun T => by
  change ‖∑' i, inner ℝ (b i) (T.val (b i))‖ ≤ 1*‖T‖
  rw [one_mul]
  have hs : Summable (fun i => ‖inner ℝ (b i) (T.val (b i))‖) := by
    simpa only [Real.norm_eq_abs] using (traceClass_diagonal_summable b T).1
  exact (norm_tsum_le_tsum_norm hs).trans
    (by simpa only [Real.norm_eq_abs] using (traceClass_diagonal_summable b T).2))

/--
Exact identity `trace b T = ∑' i, inner ℝ (b i) (T.val (b i))`.

Use: `chebyshev2.Continuum.TraceClassOperator.trace_rankOne` rewrites with this identity to
establish exact identity `trace b ⟨InnerProductSpace.rankOne ℝ a d, rankOne_isTraceClass a d⟩ =
inner ℝ a d`.

Article: chebyshev2, Lemma 4 via `chebyshev2.Continuum.TraceClassOperator.trace_rankOne`.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem trace_apply (T : TraceClassOperator E) :
    trace b T = ∑' i, inner ℝ (b i) (T.val (b i)) := rfl

/--
Exact identity `trace b ⟨InnerProductSpace.rankOne ℝ a d, rankOne_isTraceClass a d⟩ = inner ℝ a
d`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 4.

Source: Simon, Trace Ideals and Their Applications — trace and diagonal summation for
trace-class operators.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem trace_rankOne (a d : E) :
    trace b ⟨InnerProductSpace.rankOne ℝ a d, rankOne_isTraceClass a d⟩ = inner ℝ a d := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [trace_apply]
  have h := b.hasSum_inner_mul_inner a d
  convert h.tsum_eq using 1
  apply tsum_congr
  intro i
  change inner ℝ (b i) ((InnerProductSpace.rankOne ℝ a d) (b i)) = _
  simp only [InnerProductSpace.rankOne_apply, real_inner_smul_right]
  rw [real_inner_comm (b i) a, real_inner_comm d (b i), mul_comm]

end TraceClassOperator
end
end chebyshev2.Continuum
