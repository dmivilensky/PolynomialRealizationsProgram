import krylov.Numerics.HalfBarrierWitness
import krylov.Numerics.HalfBarrierComparison

/-!
Article: main_krylov, apC:prop:digits, certified five-significant-digit variant.
Two explicit rational polynomial barriers enclose the actual separating graph.
The root isolation, derivative algebra and Bernstein residual certificates are
checked in the kernel; they require no external interval-arithmetic assumption.
Source: the polynomial differential-barrier method, applied to the actual
analytic LV graph constructed in stage 9.
-/

/-!
Article: krylov, Proposition D.14 [apC:prop:digits].

The exact printed rational crossing brackets, their actual four orbit exits and all seven
strict five-significant-digit roundings follow from kernel-checked rational barriers.
The new half-gamma exit adapters use the stronger printed endpoints, not merely their coarser
five-digit relaxation.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set

namespace SubcriticalGraph
variable (G : SubcriticalGraph (1 / 2))

/-- The exact numerical upper witness controls the genuine global branch. -/
theorem half_certified_upper_barrier {U : ℝ} (hU : U ∈ Ico (1 : ℝ) 4) :
    G.σ U < halfCertifiedBarrier 1 U := by
  have hh := G.half_signed_barrier (b := halfCertifiedBarrier 1)
    (b' := halfCertifiedBarrierDerivative 1) (sign := 1)
    (by norm_num) (halfCertifiedBarrier_four 1)
    (halfCertifiedBarrier_hasDerivAt 1) ?_
    (fun U hU ↦ halfCertifiedBarrier_upper_residual ⟨hU.1,hU.2.le⟩ hU.2) hU
  · simpa only [one_mul, sub_pos] using hh
  · intro r hr hp
    have hb := half_saddle_root_bounds hr hp
    norm_num [halfCertifiedBarrierDerivative, halfCertifiedP]
    linarith [hb.1]

/-- The exact numerical lower witness controls the genuine global branch. -/
theorem half_certified_lower_barrier {U : ℝ} (hU : U ∈ Ico (1 : ℝ) 4) :
    halfCertifiedBarrier (-1) U < G.σ U := by
  have hh := G.half_signed_barrier (b := halfCertifiedBarrier (-1))
    (b' := halfCertifiedBarrierDerivative (-1)) (sign := -1)
    (by norm_num) (halfCertifiedBarrier_four (-1))
    (halfCertifiedBarrier_hasDerivAt (-1)) ?_
    (fun U hU ↦ halfCertifiedBarrier_lower_residual ⟨hU.1,hU.2.le⟩ hU.2) hU
  · nlinarith
  · intro r hr hp
    have hb := half_saddle_root_bounds hr hp
    norm_num [halfCertifiedBarrierDerivative, halfCertifiedP]
    linarith [hb.2]

/-- A literal rational enclosure of the actual half-gamma crossing.
Its width already suffices for all agreed five-significant-digit constants. -/
theorem half_certified_crossing_bounds :
    (1765356/1000000 : ℝ) < G.σ 1 ∧ G.σ 1 < (1765358/1000000 : ℝ) := by
  have hl := G.half_certified_lower_barrier (by norm_num : (1 : ℝ) ∈ Ico 1 4)
  have hu := G.half_certified_upper_barrier (by norm_num : (1 : ℝ) ∈ Ico 1 4)
  norm_num [halfCertifiedBarrier, halfCertifiedP] at hl hu
  constructor <;> linarith

/-- The common five-significant-digit interface for the exact scalar constants. -/
theorem half_certified_five_digit_bounds :
    (176535/100000 : ℝ) < G.σ 1 ∧ G.σ 1 < (176536/100000 : ℝ) := by
  have hh := G.half_certified_crossing_bounds
  constructor <;> linarith [hh.1, hh.2]

end SubcriticalGraph
end
end krylov.LotkaVolterra
