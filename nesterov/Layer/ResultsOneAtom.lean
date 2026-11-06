import nesterov.Layer.OneAtom
import nesterov.Layer.ConsequencesAlgebra
import nesterov.TwoStep.Kappa

/-! The source's dashed one-atom ceiling, including the flow ceiling and
the literal condition-number variable. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology

private theorem limsup_le_of_eventual_real_bounds {A : Type*} {l : Filter A}
    {f : A→ℝ} {b : ℝ} (h : ∀ d : ℝ,b<d → ∀ᶠ a in l,f a≤d) :
    limsup (fun a=>(f a:EReal)) l≤(b:EReal) := by
  by_contra hn
  obtain ⟨d,hd,hdlim⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have hb : ∀ᶠ a in l,(f a:EReal)≤(d:EReal) := by
    filter_upwards [h d (EReal.coe_lt_coe_iff.mp hd)] with a ha
    exact EReal.coe_le_coe_iff.mpr ha
  exact (not_lt_of_ge (Filter.limsup_le_of_le (by isBoundedDefault) hb)) hdlim

variable {A : Type*} {l : Filter A} {θ y : ℝ} (F : Scaling A l θ y (1/2))

theorem layer_one_atom_limsup [l.IsCountablyGenerated] {B : ℝ}
    (hy2 : y<2) (hBp : 0<B) (hB : Tendsto F.layerDeficit l (𝓝 B))
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    limsup (fun a=>(F.restCoefficientAt a:EReal)) l≤(Layer.mixedConstant θ y B:EReal) := by
  have hflow : limsup (fun a=>(F.restCoefficientAt a:EReal)) l≤(Flow.cF θ y:EReal) :=
    limsup_le_of_eventual_real_bounds fun _ hb=>F.rest_coefficient_eventually_le_filter hstable hb
  have hatom : limsup (fun a=>(F.restCoefficientAt a:EReal)) l≤
      ((max (Layer.Lambda θ y B) 0/2:ℝ):EReal) :=
    limsup_le_of_eventual_real_bounds fun _ hb=>F.layer_one_atom_coefficient_le hy2 hBp hB hstable hb
  rcases le_total (Flow.cF θ y) (max (Layer.Lambda θ y B) 0/2) with h|h
  · simpa only [Layer.mixedConstant,min_eq_left h] using hflow
  · simpa only [Layer.mixedConstant,min_eq_right h] using hatom

end
end nesterov.TwoStep.Scaling

namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology
variable {θ y : ℝ} (F : Scaling ℝ (𝓝[>] (0:ℝ)) θ y (1/2))

private theorem restKappaCoefficient_eq_coefficientAt (he : F.epsilon=id)
    {κ : ℝ} (hκ : 0<κ) :
    F.restKappaCoefficient κ=F.restCoefficientAt (Slow.epsilon κ) := by
  let R : ℝ→ℝ := fun μ=>Momentum.momentumRestRate (F.tuning (Slow.epsilon κ)).beta
    (F.tuning (Slow.epsilon κ)).tau (F.tuning (Slow.epsilon κ)).stepSize
    (F.tuning (Slow.epsilon κ)).step_pos.ne' μ 1
  change Real.sqrt κ*(1-R (1/κ))=
    (1-R (F.epsilon (Slow.epsilon κ)^2))/F.epsilon (Slow.epsilon κ)
  have hε : F.epsilon (Slow.epsilon κ)=Slow.epsilon κ := congrFun he _
  have hμ : F.epsilon (Slow.epsilon κ)^2=1/κ :=
    (congrArg (fun x : ℝ=>x^2) hε).trans (Slow.epsilon_sq hκ.le)
  calc
    _=(1-R (1/κ))/Slow.epsilon κ := (Slow.coefficient_kappa hκ).symm
    _=_ := congrArg₂ (fun n d : ℝ=>n/d)
      (congrArg (fun x : ℝ=>1-x) (congrArg R hμ)).symm hε.symm

theorem layer_one_atom_kappa_limsup (he : F.epsilon=id) {B : ℝ}
    (hy2 : y<2) (hBp : 0<B) (hB : Tendsto F.layerDeficit (𝓝[>] (0:ℝ)) (𝓝 B))
    (hstable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1) :
    limsup (fun κ=>(F.restKappaCoefficient κ:EReal)) atTop≤(Layer.mixedConstant θ y B:EReal) := by
  have hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (F.epsilon ε^2) 1 := by
    simpa only [he,id_eq] using hstable
  have h := F.layer_one_atom_limsup hy2 hBp hB hs
  calc
    _=limsup (fun κ=>(F.restCoefficientAt (Slow.epsilon κ):EReal)) atTop := by
      apply limsup_congr
      filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
      exact congrArg (fun r : ℝ=>(r:EReal))
        (F.restKappaCoefficient_eq_coefficientAt he hκ)
    _=limsup (fun ε=>(F.restCoefficientAt ε:EReal)) (𝓝[>] (0:ℝ)) :=
      Slow.epsilon_limsup (fun ε : ℝ=>(F.restCoefficientAt ε:EReal))
    _≤_ := h

end
end nesterov.TwoStep.Scaling
