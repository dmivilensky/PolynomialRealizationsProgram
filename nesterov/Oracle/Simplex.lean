import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Algebra.Monoid.FunOnFinite
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! The finite probability simplex and its affine moment map. -/
namespace nesterov.Oracle
noncomputable section
open Set
open scoped BigOperators
variable {I E : Type*} [Fintype I]

def Weights (I : Type*) [Fintype I] : Set (I→ℝ) :=
  {α | (∀ i,0≤α i) ∧ ∑ i,α i=1}

theorem weights_bound {α : I→ℝ} (hα : α∈Weights I) (i : I) : α i∈Icc (0:ℝ) 1 := by
  exact ⟨hα.1 i,hα.2 ▸ Finset.single_le_sum (fun j _=>hα.1 j) (Finset.mem_univ i)⟩

theorem weights_closed : IsClosed (Weights I) := by
  have he : Weights I=(⋂ i,{α : I→ℝ | 0≤α i})∩{α | ∑ i,α i=1} := by
    ext α
    simp only [Weights,mem_inter_iff,mem_iInter,mem_ofPred_eq]
  rw [he]
  apply IsClosed.inter
  · exact isClosed_iInter (fun i=>isClosed_le continuous_const (continuous_apply i))
  · exact isClosed_eq (by fun_prop) continuous_const

theorem weights_compact : IsCompact (Weights I) := by
  apply IsCompact.of_isClosed_subset isCompact_Icc weights_closed
  intro α hα
  exact ⟨fun i=>(weights_bound hα i).1,fun i=>(weights_bound hα i).2⟩

theorem weights_single [DecidableEq I] (i : I) : Pi.single i (1:ℝ)∈Weights I := by
  classical
  constructor
  · intro j
    by_cases h : j=i <;> simp [h]
  · simp

theorem weights_mix {α β : I→ℝ} (hα : α∈Weights I) (hβ : β∈Weights I)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : (1-t) • α+t • β∈Weights I := by
  constructor
  · intro i
    exact add_nonneg (mul_nonneg (by linarith [ht.2]) (hα.1 i)) (mul_nonneg ht.1 (hβ.1 i))
  · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
      ←Finset.mul_sum,hα.2,hβ.2,mul_one]
    ring

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

def moment (v : I→E) (α : I→ℝ) : E := ∑ i,α i • v i
def height (b : I→ℝ) (α : I→ℝ) : ℝ := ∑ i,α i*b i

theorem moment_mix (v : I→E) (α β : I→ℝ) (t : ℝ) :
    moment v ((1-t) • α+t • β)=(1-t) • moment v α+t • moment v β := by
  simp only [moment,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_smul,mul_smul,
    Finset.sum_add_distrib,Finset.smul_sum]

theorem height_mix (b : I→ℝ) (α β : I→ℝ) (t : ℝ) :
    height b ((1-t) • α+t • β)=(1-t)*height b α+t*height b β := by
  simp only [height,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,mul_assoc,
    Finset.sum_add_distrib,Finset.mul_sum]

theorem continuous_moment (v : I→E) : Continuous (moment v) := by unfold moment;fun_prop
theorem continuous_height (b : I→ℝ) : Continuous (height b) := by unfold height;fun_prop

theorem moment_single [DecidableEq I] (v : I→E) (i : I) : moment v (Pi.single i 1)=v i := by
  classical
  simp [moment,Pi.single_apply]

theorem height_single [DecidableEq I] (b : I→ℝ) (i : I) : height b (Pi.single i 1)=b i := by
  classical
  simp [height,Pi.single_apply]

end
end nesterov.Oracle
