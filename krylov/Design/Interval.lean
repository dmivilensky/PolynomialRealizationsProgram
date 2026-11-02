import krylov.Design.AtomicBridge
import chebyshev1.Chebyshev.Normalization

/-!
Article: main_krylov, thm:B, the original physical interval design problem.
Use: specialize the compact-measure construction at the article's exterior point
zero, and connect it to the same finite spectral measures used by the CG proofs.
Source: the proved compact-measure existence and finite Christoffel dictionary.
-/

namespace krylov.Design
noncomputable section
open MeasureTheory jacobi.Finite

/-- The article's actual closed spectral interval as a compact space.
Article: main_krylov, thm:B. -/
abbrev Spectrum (I : chebyshev1.SpectralInterval) := Set.Icc I.mu I.L

/-- The physical spectral coordinate, without a change of the extrapolation point.
Article: main_krylov, thm:B. -/
def spectralCoordinate (I : chebyshev1.SpectralInterval) : C(Spectrum I, ℝ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The exact original mixed design functional Phi(w,gamma).
Article: main_krylov, thm:B. -/
def intervalObjective (I : chebyshev1.SpectralInterval) (M : ℕ) (w : Fin M → ℝ) (γ : ℝ)
    (ν : ProbabilityMeasure (Spectrum I)) : ℝ :=
  mixedObjective M w γ 0 (spectralCoordinate I) ν

/-- The original physical-interval objective attains its maximum, with all degeneracies admitted.
Article: main_krylov, thm:B, attainment.
Proof: the lower endpoint witnesses nonemptiness; use imported compactness through the proved objective. -/
theorem intervalObjective_attains (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∃ ν : ProbabilityMeasure (Spectrum I), ∀ η,
      intervalObjective I M w γ η ≤ intervalObjective I M w γ ν := by
  have : Nonempty (Spectrum I) := ⟨⟨I.mu, le_rfl, I.mu_lt_L.le⟩⟩
  exact mixedObjective_attains M w hw hγ 0 (spectralCoordinate I)

/-- Genuine finite physical spectral data give exactly the original reciprocal Christoffel kernel.
Article: main_krylov, thm:B, bridge to the already proved CG response.
Proof: realize each original node in the interval and invoke the genuine finite-measure dictionary. -/
theorem interval_christoffel_atomic {N m : ℕ} (I : chebyshev1.SpectralInterval)
    (M : DiscreteMeasure N) (hM : ∀ i, M.node i ∈ Set.Icc I.mu I.L) (hm : m < N) :
    christoffel m 0 (spectralCoordinate I)
      (atomicProbability M (fun i => ⟨M.node i, hM i⟩ : Fin N → Spectrum I)) =
      (Reference.christoffelKernel M m 0)⁻¹ :=
  christoffel_atomic M hm _ (spectralCoordinate I) (fun _ => rfl) 0

end
end krylov.Design
