import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! A finite family of strict integral inequalities has a finite atomic
realization on the same carrier. No approximation of the carrier is needed. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Set
open scoped BigOperators

theorem finite_strict_moments_on {X I : Type*} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X→I→ℝ) (S : Set X)
    (hS : ∀ᵐ x ∂μ,x∈S) (hf : ∀ i,Integrable (fun x=>f x i) μ)
    (hpos : ∀ i,0<∫ x,f x i ∂μ) :
    ∃ (J : Type) (_ : Fintype J) (w : J→ℝ) (x : J→X),
      (∀ j,0≤w j) ∧ (∑ j,w j)=1 ∧ (∀ j,x j∈S) ∧
        ∀ i,0<∑ j,w j*f (x j) i := by
  classical
  have hint : Integrable f μ := Integrable.of_eval hf
  have hc : (∫ x,f x ∂μ)∈closure (convexHull ℝ (f '' S)) :=
    (convex_convexHull ℝ (f '' S)).closure.integral_mem isClosed_closure
      (hS.mono fun x hx=>subset_closure (subset_convexHull ℝ (f '' S) ⟨x,hx,rfl⟩)) hint
  let U : Set (I→ℝ) := {z | ∀ i,0<z i}
  have hU : IsOpen U := by
    dsimp only [U]
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i=>isOpen_lt continuous_const (continuous_apply i)
  have hmean : (∫ x,f x ∂μ)∈U := by
    intro i
    rw [eval_integral hf]
    exact hpos i
  obtain ⟨z,hzpos,hz⟩ := mem_closure_iff.mp hc U hU hmean
  obtain ⟨J,hJ,w,v,hw,hs,hv,hvz⟩ := mem_convexHull_iff_exists_fintype.mp hz
  let x : J→X := fun j=>Classical.choose (hv j)
  have hx (j : J) : x j∈S ∧ f (x j)=v j := Classical.choose_spec (hv j)
  refine ⟨J,hJ,w,x,hw,hs,fun j=>(hx j).1,?_⟩
  intro i
  have he := congrFun hvz i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at he
  have he' : (∑ j,w j*f (x j) i)=z i := by
    simpa only [(hx _).2] using he
  rw [he']
  exact hzpos i

theorem finite_strict_moments {X I : Type*} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X→I→ℝ)
    (hf : ∀ i,Integrable (fun x=>f x i) μ)
    (hpos : ∀ i,0<∫ x,f x i ∂μ) :
    ∃ (J : Type) (_ : Fintype J) (w : J→ℝ) (x : J→X),
      (∀ j,0≤w j) ∧ (∑ j,w j)=1 ∧ ∀ i,0<∑ j,w j*f (x j) i := by
  classical
  have hint : Integrable f μ := Integrable.of_eval hf
  have hc : (∫ x,f x ∂μ)∈closure (convexHull ℝ (range f)) :=
    (convex_convexHull ℝ (range f)).closure.integral_mem isClosed_closure
      (ae_of_all μ fun x=>subset_closure (subset_convexHull ℝ (range f) (mem_range_self x))) hint
  let U : Set (I→ℝ) := {z | ∀ i,0<z i}
  have hU : IsOpen U := by
    dsimp only [U]
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i=>isOpen_lt continuous_const (continuous_apply i)
  have hmean : (∫ x,f x ∂μ)∈U := by
    intro i
    rw [eval_integral hf]
    exact hpos i
  obtain ⟨z,hzpos,hz⟩ := mem_closure_iff.mp hc U hU hmean
  obtain ⟨J,hJ,w,v,hw,hs,hv,hvz⟩ := mem_convexHull_iff_exists_fintype.mp hz
  let x : J→X := fun j=>Classical.choose (hv j)
  have hx (j : J) : f (x j)=v j := Classical.choose_spec (hv j)
  refine ⟨J,hJ,w,x,hw,hs,?_⟩
  intro i
  have he := congrFun hvz i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at he
  have he' : (∑ j,w j*f (x j) i)=z i := by
    simpa only [hx] using he
  rw [he']
  exact hzpos i

end
end nesterov.Spread
