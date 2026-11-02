import jacobi.Variational.Congruence
import jacobi.Variational.Tails
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
Article: jacobi, Theorem D.7.
Continuity upgrades the almost-everywhere Euler representative to the full
pointwise symmetric decreasing class. The original minimizer need only be
measurable. Dense full-measure equality sets transfer the two-point order,
so no unsupported pointwise monotonicity is assumed after replacement.
Source: full support of Lebesgue measure and continuity of the Euler representative.
Use: retains the original minimizer's exact radial class when its Green Euler formula supplies classical regularity.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
set_option backward.isDefEq.respectTransparency false

/-- A continuous a.e. representative of an actual symmetric decreasing density is itself symmetric decreasing pointwise.
Use: retains the original minimizer's exact radial class when its Green Euler formula supplies classical regularity.
Article: jacobi, Theorem D.7.
Proof: reflect the a.e. equality and use continuity for evenness. If the
two-point monotonicity failed, continuity would give an open product region
of failure. Its intersection with the dense product equality set contradicts
the original pointwise radial order. -/
theorem continuous_radial {m f : ℝ → ℝ} (hm : SymmetricDecreasing m) (hf : Continuous f)
    (he : m=ᵐ[volume] f) : SymmetricDecreasing f := by
  -- A null-set replacement is upgraded by full measure and actual continuity, not by redefining the radial class.
  have hneg := (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp he
  have heven : (fun x => f (-x))=ᵐ[volume] f := by
    filter_upwards [he,hneg] with x hx hn
    change m (-x)=f (-x) at hn
    exact hn.symm.trans ((hm.even x).trans hx)
  refine ⟨fun x => congrFun (Measure.eq_of_ae_eq heven (hf.comp continuous_neg) hf) x,?_⟩
  intro x hx y _hy hxy
  rcases eq_or_lt_of_le hxy with heq | hlt
  · rw [heq]
  · by_contra! hrev
    let U : Set (ℝ × ℝ) := {z | 0<z.1 ∧ z.1<z.2 ∧ f z.1<f z.2}
    have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter (isOpen_lt (hf.comp continuous_fst) (hf.comp continuous_snd)))
    obtain ⟨z,hz,hzu⟩ := ((volume.dense_of_ae he).prod (volume.dense_of_ae he)).exists_mem_open hU
      ⟨(x,y),hx,hlt,hrev⟩
    have hmono := hm.decreasing hzu.1 (hzu.1.trans hzu.2.1) hzu.2.1.le
    rw [hz.1,hz.2] at hmono
    exact hzu.2.2.not_ge hmono

end
end jacobi.Fredholm
