import «2610.05164v2».Continuum.GramSpectrum

/-!
Article: 2610.05164v2, Lemma 4.
Compactness of A* A implies compactness of A.
Use: `«2610.05164v2».Continuum.kernelOperator_isCompact` feeds
`«2610.05164v2».HalfLine.operator_compact` (operator compact).
Proof chain: `«2610.05164v2».Packing.packedKernel_hasSum_square_trace` — 2610.05164v2, Theorem 2.4;
Uniform l1 spectral transfer, ground parameter and Fredholm/cosh observations.
Source: Riesz and Sz.-Nagy, Functional Analysis — nonzero spectra of Gram operators. The needed form
is proved here.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open Set Metric
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

/--
The stated quantitative bound `‖A x - A y‖^2 ≤ ‖x-y‖ * ‖(A.adjoint ∘L A) x - (A.adjoint ∘L A)
y‖`.

Use: `«2610.05164v2».Continuum.isCompact_of_adjoint_comp` uses this bound to establish
compactness of the displayed operator: `IsCompactOperator A`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Source: Riesz and Sz.-Nagy, Functional Analysis — nonzero spectra of Gram operators.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem gram_distance_sq (A : E →L[ℝ] F) (x y : E) :
    ‖A x - A y‖^2 ≤ ‖x-y‖ * ‖(A.adjoint ∘L A) x - (A.adjoint ∘L A) y‖ := by
  rw [← map_sub, ← map_sub]
  have he : ‖A (x-y)‖^2 = inner ℝ (x-y) ((A.adjoint ∘L A) (x-y)) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      real_inner_self_eq_norm_sq]
  rw [he]
  exact real_inner_le_norm _ _

/--
Compactness of A* A implies compactness of A. The proof transfers finite covers of the Gram
image using its quadratic distance estimate.

Compactness of the displayed operator: `IsCompactOperator A`.

Use: `«2610.05164v2».Continuum.evaluationOperator_isCompact` uses this assertion to establish
compactness of the displayed operator: `IsCompactOperator (evaluationOperator hm hn)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Source: Riesz and Sz.-Nagy, Functional Analysis — nonzero spectra of Gram operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.gram_distance_sq` with the
arguments shown in the proof.
-/
theorem isCompact_of_adjoint_comp (A : E →L[ℝ] F)
    (hA : IsCompactOperator (A.adjoint ∘L A)) : IsCompactOperator A := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.gram_distance_sq` with the
  -- arguments shown in the proof.
  classical
  have ht := (hA.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  have hb : TotallyBounded (A '' closedBall 0 1) := by
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    obtain ⟨t, hts, htf, hcover⟩ := Metric.finite_approx_of_totallyBounded ht
      (ε^2/2) (by positivity)
    have hr (y : t) : ∃ x ∈ closedBall (0 : E) 1, (A.adjoint ∘L A) x = (y : E) := hts y.property
    choose r hrb hre using hr
    let : Fintype t := htf.fintype
    refine ⟨range (fun y : t => A (r y)), finite_range _, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hc := hcover (mem_image_of_mem (A.adjoint ∘L A) hx)
    simp only [mem_iUnion] at hc ⊢
    obtain ⟨y, hy, hxy⟩ := hc
    refine ⟨A (r ⟨y, hy⟩), ⟨⟨y, hy⟩, rfl⟩, ?_⟩
    have hdist : ‖(A.adjoint ∘L A) x - (A.adjoint ∘L A) (r ⟨y,hy⟩)‖ < ε^2/2 := by
      rw [hre]
      simpa only [dist_eq_norm] using mem_ball.mp hxy
    have hx' : ‖x‖ ≤ 1 := by simpa using mem_closedBall.mp hx
    have hr' : ‖r ⟨y,hy⟩‖ ≤ 1 := by simpa using mem_closedBall.mp (hrb ⟨y,hy⟩)
    have hd : ‖x-r ⟨y,hy⟩‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
    have he := (gram_distance_sq A x (r ⟨y,hy⟩)).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
    rw [mem_ball, dist_eq_norm]
    nlinarith [norm_nonneg (A x - A (r ⟨y,hy⟩))]
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall
    A.toLinearMap zero_lt_one).mpr (hb.closure.isCompact_of_isClosed isClosed_closure)

/--
Compactness of the displayed operator: `IsCompactOperator (evaluationOperator hm hn)`.

Use: `«2610.05164v2».Continuum.kernelOperator_isCompact` uses this assertion to establish
compactness of the displayed operator: `IsCompactOperator (kernelOperator hm hn)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Source: Riesz and Sz.-Nagy, Functional Analysis — nonzero spectra of Gram operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.isCompact_of_adjoint_comp`,
`«2610.05164v2».Continuum.evaluationOperator_adjoint_comp`,
`«2610.05164v2».Continuum.densityOperator_isCompact` with the arguments shown in the proof.
-/
theorem evaluationOperator_isCompact {m : ℝ → ℝ} (hm : MeasureTheory.Integrable m)
    (hn : ∀ x, 0 ≤ m x) : IsCompactOperator (evaluationOperator hm hn) := by
  apply isCompact_of_adjoint_comp
  rw [evaluationOperator_adjoint_comp]
  exact densityOperator_isCompact hm

/--
Compactness of the displayed operator: `IsCompactOperator (kernelOperator hm hn)`.

Use: `«2610.05164v2».Continuum.kernelSpectralData` uses this assertion in the displayed
construction of `kernelSpectralData`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Source: Riesz and Sz.-Nagy, Functional Analysis — nonzero spectra of Gram operators.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.evaluationOperator_isCompact`
with the arguments shown in the proof.
-/
theorem kernelOperator_isCompact {m : ℝ → ℝ} (hm : MeasureTheory.Integrable m)
    (hn : ∀ x, 0 ≤ m x) : IsCompactOperator (kernelOperator hm hn) :=
  (evaluationOperator_isCompact hm hn).comp_clm _

end
end «2610.05164v2».Continuum
