import krylov.Strings.TailKernels
import Mathlib.Topology.Algebra.Module.Basic

/-!
Article: main_krylov, apC:prop:tauber, density of Stieltjes test kernels.
Use: actual Stieltjes transform limits determine the scaled spectral measure.
Partial fractions put products of distinct kernels in their linear span;
continuity handles repeated parameters. The closed span is therefore a
separating real algebra, so mathlib Stone-Weierstrass makes it the whole space.
Source: the resolvent-algebra proof of the Stieltjes continuity theorem.
-/

namespace krylov.Strings.Tail
noncomputable section
open Set Filter
open scoped Topology

/-- The algebraic linear span of the compactified Stieltjes test kernels. -/
def kernelSpan : Submodule ℝ C(UnitInterval, ℝ) :=
  Submodule.span ℝ (range kernel)

/-- Its uniform closure, before multiplication closure has been proved. -/
def closedKernelSpan : Submodule ℝ C(UnitInterval, ℝ) := kernelSpan.topologicalClosure

/-- Every actual Stieltjes kernel lies in the closed linear span. -/
theorem kernel_mem_closedSpan (a : PositiveParameter) : kernel a ∈ closedKernelSpan :=
  kernelSpan.le_topologicalClosure (Submodule.subset_span (mem_range_self a))

private theorem kernel_mul_mem_of_ne (a b : PositiveParameter) (hab : a ≠ b) :
    kernel a * kernel b ∈ closedKernelSpan := by
  rw [kernel_mul_of_ne a b hab]
  exact closedKernelSpan.add_mem
    (closedKernelSpan.smul_mem _ (kernel_mem_closedSpan a))
    (closedKernelSpan.smul_mem _ (kernel_mem_closedSpan b))

/-- Products of arbitrary kernels lie in their closed linear span, including
the diagonal case obtained by actual uniform convergence. -/
theorem kernel_mul_mem_closedSpan (a b : PositiveParameter) :
    kernel a * kernel b ∈ closedKernelSpan := by
  by_cases hab : a = b
  · subst b
    let b : ℕ → PositiveParameter := fun n ↦
      ⟨(a : ℝ) + 1 / ((n : ℝ) + 1), by
        change 0 < (a : ℝ) + 1 / ((n : ℝ) + 1)
        exact add_pos a.property (by positivity)⟩
    have hb : Tendsto b atTop (𝓝 a) := by
      apply tendsto_subtype_rng.mpr
      simpa only [b, add_zero] using
        (tendsto_const_nhds (x := (a : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun n ↦ kernel a * kernel (b n)) atTop (𝓝 (kernel a * kernel a)) :=
      tendsto_const_nhds.mul (kernel_continuous.tendsto a |>.comp hb)
    apply kernelSpan.isClosed_topologicalClosure.mem_of_tendsto hlim
    exact Eventually.of_forall fun n ↦ kernel_mul_mem_of_ne a (b n) (by
      intro he
      have hh := congrArg Subtype.val he
      dsimp [b] at hh
      have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith)
  · exact kernel_mul_mem_of_ne a b hab

private def multiplicationPreimage (S : Submodule ℝ C(UnitInterval, ℝ))
    (f : C(UnitInterval, ℝ)) : Submodule ℝ C(UnitInterval, ℝ) where
  carrier := {g | f * g ∈ S}
  zero_mem' := by
    change f * 0 ∈ S
    simpa only [mul_zero] using S.zero_mem
  add_mem' := by
    intro g h hg hh
    change f * (g + h) ∈ S
    simpa only [mul_add] using S.add_mem hg hh
  smul_mem' := by
    intro c g hg
    change f * (c • g) ∈ S
    simpa only [mul_smul_comm] using S.smul_mem c hg

private theorem multiplicationPreimage_closed (f : C(UnitInterval, ℝ)) :
    IsClosed (multiplicationPreimage closedKernelSpan f : Set C(UnitInterval, ℝ)) :=
  kernelSpan.isClosed_topologicalClosure.preimage (continuous_const.mul continuous_id)

/-- Uniform closure and linearity extend the kernel product identity to all
elements of their closed span. -/
theorem closedKernelSpan_mul_mem {f g : C(UnitInterval, ℝ)}
    (hf : f ∈ closedKernelSpan) (hg : g ∈ closedKernelSpan) :
    f * g ∈ closedKernelSpan := by
  have hkernel (a : PositiveParameter) :
      closedKernelSpan ≤ multiplicationPreimage closedKernelSpan (kernel a) := by
    apply kernelSpan.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨b, rfl⟩
      exact kernel_mul_mem_closedSpan a b
    · exact multiplicationPreimage_closed _
  have hright : closedKernelSpan ≤ multiplicationPreimage closedKernelSpan g := by
    apply kernelSpan.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      change g * kernel a ∈ closedKernelSpan
      rw [mul_comm]
      exact hkernel a hg
    · exact multiplicationPreimage_closed _
  have hh : g * f ∈ closedKernelSpan := hright hf
  simpa only [mul_comm] using hh

/-- The compactified Stieltjes kernels have dense real linear span. No
polynomial moment convergence or Tauberian theorem is assumed. -/
theorem closedKernelSpan_eq_top : closedKernelSpan = ⊤ := by
  have hOne : (1 : C(UnitInterval, ℝ)) ∈ closedKernelSpan := by
    simpa only [kernel_one] using kernel_mem_closedSpan ⟨1, by norm_num⟩
  let A : Subalgebra ℝ C(UnitInterval, ℝ) := {
    carrier := closedKernelSpan
    zero_mem' := closedKernelSpan.zero_mem
    one_mem' := hOne
    add_mem' := closedKernelSpan.add_mem
    mul_mem' := closedKernelSpan_mul_mem
    algebraMap_mem' r := by
      change (algebraMap ℝ C(UnitInterval, ℝ)) r ∈ closedKernelSpan
      rw [Algebra.algebraMap_eq_smul_one]
      exact closedKernelSpan.smul_mem r hOne }
  have hSep : A.SeparatesPoints := by
    intro u v huv
    refine ⟨kernel ⟨2, by norm_num⟩, ?_, ?_⟩
    · exact ⟨kernel ⟨2, by norm_num⟩, kernel_mem_closedSpan _, rfl⟩
    · exact fun he ↦ huv (kernel_two_injective he)
  have hDense := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hSep
  have hClosed : A.topologicalClosure = A := by
    apply SetLike.coe_injective
    rw [Subalgebra.topologicalClosure_coe]
    exact closure_eq_iff_isClosed.mpr kernelSpan.isClosed_topologicalClosure
  rw [hClosed] at hDense
  apply SetLike.ext
  intro f
  change f ∈ A ↔ f ∈ (⊤ : Subalgebra ℝ C(UnitInterval, ℝ))
  rw [hDense]

end
end krylov.Strings.Tail
