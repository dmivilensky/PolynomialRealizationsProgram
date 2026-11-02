import krylov.Strings.TailKernelDensity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
Article: main_krylov, apC:prop:tauber, the Stieltjes continuity step.
Use: identify genuine finite measures from their compactified Stieltjes
integrals and turn convergence of those integrals into weak convergence.
Source: the proved dense kernel span, mathlib L1 integration, finite-measure
weak compactness on a compact space and uniqueness of cluster points.
-/

namespace krylov.Strings.Tail
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Integration of compact continuous tests as an actual continuous linear
functional, obtained from mathlib's L1 embedding and integral. -/
def compactIntegral (μ : FiniteMeasure UnitInterval) : C(UnitInterval, ℝ) →L[ℝ] ℝ :=
  L1.integralCLM.comp (ContinuousMap.toLp 1 (μ : Measure UnitInterval) ℝ)

/-- The constructed continuous linear functional is the ordinary integral. -/
theorem compactIntegral_apply (μ : FiniteMeasure UnitInterval) (f : C(UnitInterval, ℝ)) :
    compactIntegral μ f = ∫ u, f u ∂μ := by
  rw [compactIntegral, ContinuousLinearMap.comp_apply, ← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (μ : Measure UnitInterval) (𝕜 := ℝ) f)

/-- Finite measures on the compactified spectral axis are determined by the
actual Stieltjes kernels alone. -/
theorem eq_of_kernel_integrals {μ ν : FiniteMeasure UnitInterval}
    (h : ∀ a : PositiveParameter, ∫ u, kernel a u ∂μ = ∫ u, kernel a u ∂ν) : μ = ν := by
  let L := compactIntegral μ - compactIntegral ν
  have hs : kernelSpan ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change compactIntegral μ (kernel a) - compactIntegral ν (kernel a) = 0
    rw [compactIntegral_apply, compactIntegral_apply, h a, sub_self]
  have hcl : closedKernelSpan ≤ L.ker :=
    kernelSpan.topologicalClosure_minimal hs L.isClosed_ker
  rw [closedKernelSpan_eq_top] at hcl
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro f
  have hh : L f.toContinuousMap = 0 := hcl (Submodule.mem_top)
  change compactIntegral μ f.toContinuousMap - compactIntegral ν f.toContinuousMap = 0 at hh
  rw [compactIntegral_apply, compactIntegral_apply] at hh
  exact sub_eq_zero.mp hh

/-- Bounded finite measures whose compactified Stieltjes integrals converge
to those of an actual finite measure converge weakly to that measure. -/
theorem tendsto_of_kernel_integrals {ι : Type*} {F : Filter ι}
    {μ : ι → FiniteMeasure UnitInterval} {ν : FiniteMeasure UnitInterval} {C : ℝ≥0}
    (hbound : ∀ᶠ i in F, (μ i).mass ≤ C)
    (h : ∀ a : PositiveParameter,
      Tendsto (fun i ↦ ∫ u, kernel a u ∂μ i) F (𝓝 (∫ u, kernel a u ∂ν))) :
    Tendsto μ F (𝓝 ν) := by
  apply (isCompact_setOfPred_finiteMeasure_le_of_compactSpace UnitInterval C).tendsto_nhds_of_unique_mapClusterPt hbound
  intro ξ _ hξ
  apply eq_of_kernel_integrals
  intro a
  let G := 𝓝 ξ ⊓ Filter.map μ F
  have : NeBot G := hξ
  have hξlim : Tendsto (fun η : FiniteMeasure UnitInterval ↦ ∫ u, kernel a u ∂η)
      G (𝓝 (∫ u, kernel a u ∂ξ)) :=
    (FiniteMeasure.continuous_integral_continuousMap (kernel a)).tendsto ξ |>.mono_left inf_le_left
  have hνlim : Tendsto (fun η : FiniteMeasure UnitInterval ↦ ∫ u, kernel a u ∂η)
      G (𝓝 (∫ u, kernel a u ∂ν)) := by
    have hh : Tendsto (fun η : FiniteMeasure UnitInterval ↦ ∫ u, kernel a u ∂η)
        (Filter.map μ F) (𝓝 (∫ u, kernel a u ∂ν)) := h a
    exact hh.mono_left inf_le_right
  exact tendsto_nhds_unique hξlim hνlim

end
end krylov.Strings.Tail
