import krylov.LotkaVolterra.GlobalGraphAnalytic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Article: `main_krylov`, `apC:prop:LV`, regularity needed by the value-function
and fundamental-identity arguments. The actual global graph is C1 at every
positive state, including the saddle. Away from the saddle its derivative
is the continuous rational LV quotient; at the saddle analyticity has
already been proved for this very graph.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped Topology ContDiff

namespace SubcriticalGraph
variable {γ : ℝ} (G : SubcriticalGraph γ)

theorem contDiffAt_one {U : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) (hU : 0 < U) :
    ContDiffAt ℝ 1 G.σ U := by
  by_cases heq : U = saddleU γ
  · subst U
    exact (G.analyticAt_saddle hγ hγ₁).contDiffAt
  let S : Set ℝ := {U | 0 < U ∧ U ≠ saddleU γ}
  have hS : IsOpen S := isOpen_Ioi.inter isClosed_singleton.isOpen_compl
  have hGs : ContinuousOn G.σ S := (G.continuousOn hγ₁).mono fun _ ht ↦ ht.1
  have hden (V : ℝ) (hV : V ∈ S) : V * (G.σ V + 1 - V) ≠ 0 := by
    apply mul_ne_zero (ne_of_gt hV.1)
    rcases lt_or_gt_of_ne hV.2 with hlt | hgt
    · exact ne_of_gt (by linarith [(G.lower V ⟨hV.1, hlt⟩).2.2])
    · exact ne_of_lt (by linarith [(G.upper V hgt).2.2])
  have hc : ContinuousOn (fun V : ℝ ↦
      2 * G.σ V * (G.σ V - 1 - γ * V) / (V * (G.σ V + 1 - V))) S :=
    ((hGs.const_mul 2).mul ((hGs.sub continuousOn_const).sub (continuousOn_id.const_mul γ))).div
      (continuousOn_id.mul ((hGs.add continuousOn_const).sub continuousOn_id)) hden
  have hdc : ContinuousOn (deriv G.σ) S := hc.congr fun V hV ↦
    (G.derivative V hV.1 hV.2).deriv
  have hCd : ContDiffOn ℝ 1 G.σ S := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hS]
    refine ⟨fun V hV ↦ (G.derivative V hV.1 hV.2).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · norm_num
    · exact contDiffOn_zero.mpr hdc
  exact hCd.contDiffAt (hS.mem_nhds ⟨hU, heq⟩)

end SubcriticalGraph
end
end krylov.LotkaVolterra
