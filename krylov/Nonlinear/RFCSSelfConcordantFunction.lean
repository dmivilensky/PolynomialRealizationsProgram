import krylov.Nonlinear.SelfConcordantFunction
import krylov.Nonlinear.RFCSSelfConcordant
import krylov.Nonlinear.ReferenceCycleScale

/-!
Article: main_krylov, thm:RFCS, actual scalar-function cycle conclusion.
Use: State the proved nonlinear error inequality for genuine evaluations of
the actual mathematical gradient of a standard self-concordant scalar function,
with its true minimizer Hessian and original physical cycle-reference CG error.
Source: actual scalar self-concordance differential data, proved genuine
single-cycle error bound and exact actual quadratic reference scaling.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Metric krylov.Methods krylov.Reference InnerProductSpace
variable {k : ℕ}

/-- The actual finite-gradient RFC-S cycle on a standard self-concordant scalar function satisfies the printed metric-error inequality with its true last relative probe error, the original quadratic-reference penultimate error and one uniform cubic cycle remainder.
Use: Complete the genuine scalar-function single-cycle statement before applying it uniformly to actual restarted cycles.
Article: main_krylov, thm:RFCS, original self-concordant scalar-function consequence.
Proof: The self-concordant function data determine its actual Hessian and third variation, so the reference base is the true derivative of its mathematical gradient. Apply the proved physical self-concordant nonlinear error theorem. Exact genuine CG length and canonical-error homogeneity convert both the actual per-cycle probe restriction and the leading error norm to their original printed reference quantities.
-/
theorem compact_rfcs_selfConcordant_function (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ) (r B Cp : ℝ) (hr : 0<r) (hB : 0<B) (hCp : 0<Cp)
    (hsc : IsStandardSelfConcordantOn f (ball 0 r)) (h₀ : gradient f 0=0)
    (hH₀ : fderiv ℝ (gradient f) 0=cgOperator base) :
    let T := metricCoordinates base hb
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤B → cgOperator base u∈K →
      ∀ h : ℕ → ℝ, (∀ i, h i≠0) →
      (∀ i<k+1, 0<h i ∧ h i≤Cp*CG.length (cgOperator base) (cgOperator base (ε • u)) i) →
      ‖T (rfcSFunctionPoint fullMemory (gradient f) (ε • u) h (k+1))‖≤
      |1-h k/rfcSFunctionAlpha fullMemory (gradient f) (ε • u) h k| *
        ‖cgCanonicalError base (cgOperator base (ε • u)) k‖^2+C*ε^3 := by
  obtain ⟨D⟩ := hsc
  have hD₀ : D.hessian 0=cgOperator base := (D.hessian_eq_fderiv f (ball 0 r) 0 (mem_ball_self hr)).trans hH₀
  obtain ⟨ε₀,C,hε₀,hC,hbound⟩ := compact_rfcs_selfConcordant_error_bound base hb K hK hN hk
    (gradient f) D.hessian D.variation r B Cp hr hB hCp h₀ hD₀ D.gradient_derivative D.hessian_derivative D.mixed
  refine ⟨ε₀,C,hε₀,hC,?_⟩
  intro ε hε he u hu hKu h hh hrel
  have hrel' i (hi : i<k+1) : 0<h i ∧ h i≤Cp*CG.length (cgOperator base) (cgOperator base u) i := by
    have hp := hrel i hi
    rw [map_smul,reference_length_smul _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 _ ε hε.ne' i] at hp
    exact hp
  have hout := hbound ε hε he u hu hKu h hh hrel'
  rw [map_smul,metric_last_reference_error_norm base hb (cgOperator base u) (hN _ hKu) hε]
  exact hout

end
end krylov.Nonlinear
