import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
Article: chebyshev2, Proposition 2.
A measure-preserving measurable bijection induces an actual L² unitary.
Use: `chebyshev2.Continuum.measureUnitary_ae` feeds
`chebyshev2.SineContinuum.sineUnitary_ae` (sine Unitary ae).
Proof chain: `chebyshev2.SineContinuum.sine_kernel_eigenvalue` — chebyshev2, Proposition 2;
Sine coordinate bijection, symmetry, masses, spectrum, theta formula and tails.
-/
namespace chebyshev2.Continuum
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/--
A measure-preserving measurable bijection induces an actual L² unitary.

Use: `chebyshev2.Continuum.measureUnitary_ae` uses this definition to establish exact
identity `measureUnitary e he f=ᵐ[μ] f ∘ e`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def measureUnitary (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) :
    Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℝ e he) (by
    intro f
    refine ⟨Lp.compMeasurePreserving e.symm (he.symm e) f,?_⟩
    change Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm (he.symm e) f)=f
    rw [← Lp.compMeasurePreserving_comp_apply]
    have hi : (e.symm ∘ e)=id := by funext x; exact e.symm_apply_apply x
    simp only [hi,Lp.compMeasurePreserving_id_apply])

/--
Exact identity `measureUnitary e he f=ᵐ[μ] f ∘ e`.

Use: `chebyshev2.SineContinuum.affineLegendreUnitary_ae` uses this identity to establish
exact identity `affineLegendreUnitary f=ᵐ[volume] (fun t : LegendreInterval => f
(affineLegendreEquiv t)/√(1/2:ℝ))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem measureUnitary_ae (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (f : Lp ℝ 2 ν) :
    measureUnitary e he f=ᵐ[μ] f ∘ e := Lp.coeFn_compMeasurePreserving f he

end
end chebyshev2.Continuum
