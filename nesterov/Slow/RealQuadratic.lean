import nesterov.Realization.RestQuadratic
import Mathlib.Analysis.SpecificLimits.Normed

/-! Every unstable characteristic root gives an unbounded trajectory of a
literal scalar real quadratic, including nonreal characteristic roots. -/
namespace nesterov.Slow
noncomputable section
open Filter Set
open scoped Topology

theorem quadratic_wave_project (M : StationaryMethod) (ℓ : ℂ→ₗ[ℝ]ℝ)
    {lam : ℝ} {z : ℂ} (hz : M.characteristic lam z=0) :
    M.IsTrajectory (fun x : ℝ=>lam*x) (fun k=>ℓ (z^k)) := by
  intro k
  have hh := congrArg ℓ (Rates.characteristic_wave M hz k)
  change ℓ (∑ j : Fin (M.memory+1),M.recurrenceCoeff j • z^(k+j.val))=
    ℓ (lam • (∑ j : Fin M.memory,M.queryCoeff j • z^(k+j.val))) at hh
  simpa only [map_sum,map_smul,StationaryMethod.query,smul_eq_mul] using hh

theorem powers_coordinate_unbounded {z : ℂ} (hz : 1<‖z‖) :
    ¬BddAbove (range (fun n : ℕ=>|(z^n).re|)) ∨
      ¬BddAbove (range (fun n : ℕ=>|(z^n).im|)) := by
  by_contra! h
  obtain ⟨a,ha⟩ := h.1
  obtain ⟨b,hb⟩ := h.2
  have hlarge := (tendsto_pow_atTop_atTop_of_one_lt hz).eventually (eventually_gt_atTop (a+b))
  obtain ⟨n,hn⟩ := hlarge.exists
  have hre := ha (mem_range_self n)
  have him := hb (mem_range_self n)
  have hnorm := Complex.norm_le_abs_re_add_abs_im (z^n)
  rw [norm_pow] at hnorm
  linarith

theorem exists_unbounded_real_quadratic (M : StationaryMethod) {μ L lam : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hlam : lam∈Icc μ L) {z : ℂ}
    (hz : M.characteristic lam z=0) (hnorm : 1<‖z‖) :
    ∃ w : ℕ→ℝ,
      polyak.CenteredSmoothStronglyConvex μ L (fun x : ℝ=>lam/2*‖x‖^2) ∧
      M.IsTrajectory (gradient (fun x : ℝ=>lam/2*‖x‖^2)) w ∧
      ¬BddAbove (range (fun n=>‖w n‖)) := by
  have hg : gradient (fun x : ℝ=>lam/2*‖x‖^2)=(fun x : ℝ=>lam*x) :=
    funext (Momentum.real_quadratic_gradient lam)
  rcases powers_coordinate_unbounded hnorm with hre|him
  · refine ⟨fun n=>(z^n).re,Momentum.real_quadratic_centered hμ hμL hlam,?_,?_⟩
    · rw [hg]
      exact quadratic_wave_project M Complex.reCLM.toLinearMap hz
    · simpa only [Real.norm_eq_abs] using hre
  · refine ⟨fun n=>(z^n).im,Momentum.real_quadratic_centered hμ hμL hlam,?_,?_⟩
    · rw [hg]
      exact quadratic_wave_project M Complex.imCLM.toLinearMap hz
    · simpa only [Real.norm_eq_abs] using him

end
end nesterov.Slow
