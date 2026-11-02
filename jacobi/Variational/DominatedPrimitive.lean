import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
A common integrable bound for parameter derivatives on a compact interval,
together with a zero initial integrand, proves the integrability of the
integrands themselves. It also gives continuity of their actual integrals
up to zero and differentiation at every interior parameter. This avoids
assuming convergence of the determinant's spatial integral in advance.
Source: the mean value theorem and dominated Bochner differentiation in mathlib.
Use: closes convergence, zero-endpoint continuity and differentiation under the infinite spatial determinant integral at once.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A zero-based family with uniformly integrable derivatives has genuine integrals, endpoint continuity and interior integral derivatives.
Use: closes convergence, zero-endpoint continuity and differentiation under the infinite spatial determinant integral at once.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the mean value theorem bounds each integrand by b times the common
integrable derivative majorant. Dominated convergence gives closed-interval
continuity, and dominated integral differentiation applies on the interior. -/
theorem dominated_parameter_primitive (F D : ℝ → ℝ → ℝ) (B : ℝ → ℝ) {b : ℝ} (hb : 0<b)
    (hzero : ∀ x,F 0 x=0)
    (hderiv : ∀ x t,t∈Icc (0:ℝ) b → HasDerivAt (fun u => F u x) (D t x) t)
    (hbound : ∀ᵐ x : ℝ,∀ t∈Icc (0:ℝ) b,‖D t x‖≤B x) (hBi : Integrable B)
    (hFm : ∀ t∈Icc (0:ℝ) b,AEStronglyMeasurable (F t) volume)
    (hDm : ∀ t∈Icc (0:ℝ) b,AEStronglyMeasurable (D t) volume) :
    (∀ t∈Icc (0:ℝ) b,Integrable (F t)) ∧
      ContinuousOn (fun t => ∫ x,F t x) (Icc (0:ℝ) b) ∧
      ∀ t∈Ioo (0:ℝ) b,HasDerivAt (fun u => ∫ x,F u x) (∫ x,D t x) t := by
  -- The genuine mean value bound proves convergence before any integral derivative is invoked.
  have hFbound : ∀ᵐ x : ℝ,∀ t∈Icc (0:ℝ) b,‖F t x‖≤b*B x := by
    filter_upwards [hbound] with x hx
    have hB : 0≤B x := (norm_nonneg (D 0 x)).trans (hx 0 ⟨le_rfl,hb.le⟩)
    intro t ht
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hderiv x u hu).hasDerivWithinAt) (fun u hu => hx u hu)
      (convex_Icc (0:ℝ) b) (show (0:ℝ)∈Icc (0:ℝ) b from ⟨le_rfl,hb.le⟩) ht
    simp only [hzero,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] at hmvt
    rw [Real.norm_eq_abs]
    exact hmvt.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left ht.2 hB)
  have hFi (t : ℝ) (ht : t∈Icc (0:ℝ) b) : Integrable (F t) :=
    (hBi.const_mul b).mono' (hFm t ht) (hFbound.mono fun _ hx => hx t ht)
  have hcont : ContinuousOn (fun t => ∫ x,F t x) (Icc (0:ℝ) b) :=
    continuousOn_of_dominated hFm (fun t ht => hFbound.mono fun _ hx => hx t ht) (hBi.const_mul b)
      (Eventually.of_forall fun x t ht => (hderiv x t ht).continuousAt.continuousWithinAt)
  refine ⟨hFi,hcont,fun t ht => ?_⟩
  have ht' : t∈Icc (0:ℝ) b := ⟨ht.1.le,ht.2.le⟩
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (isOpen_Ioo.mem_nhds ht)
    (by filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu; exact hFm u ⟨hu.1.le,hu.2.le⟩)
    (hFi t ht') (hDm t ht')
    (hbound.mono fun x hx u hu => hx u ⟨hu.1.le,hu.2.le⟩) hBi
    (Eventually.of_forall fun x u hu => hderiv x u ⟨hu.1.le,hu.2.le⟩)).2

end
end jacobi.Variational
