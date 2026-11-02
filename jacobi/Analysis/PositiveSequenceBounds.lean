import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

/-!
Uniform positive bounds from a positive convergent sequence.
Bound the sequence and its reciprocal on their whole natural-index ranges;
the finite initial segment is included automatically by the library theorem.
Use: actual standard Jacobi norm and coefficient limits give global
endpoint and conductance bounds without separate finite certificates.
Article: jacobi, Theorem 5.4.
Article role: uniform two-sided bounds for the positive endpoint sequence.
Source: elementary real analysis: a positive sequence with positive limit is bounded above and away
from zero.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter
open scoped Topology

/-- A sequence with positive entries and a positive finite limit has
strictly positive lower and upper bounds at every natural index.
Article: jacobi, Theorem 5.4.
Source: elementary real analysis: a positive sequence with positive limit is bounded above and away
from zero.
-/
theorem positive_sequence_bounds {f : ℕ → ℝ} (hf : ∀ n,0<f n) {A : ℝ}
    (hA : 0<A) (hlim : Tendsto f atTop (𝓝 A)) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ n,c≤f n ∧ f n≤C := by
  obtain ⟨C,hC⟩ := hlim.bddAbove_range
  obtain ⟨D,hD⟩ := (hlim.inv₀ hA.ne').bddAbove_range
  have hDpos : 0<max D 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨1/(max D 1),max C 1,by positivity,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun n => ⟨?_,?_⟩⟩
  · have hd : (f n)⁻¹≤max D 1 := (hD ⟨n,rfl⟩).trans (le_max_left _ _)
    apply (div_le_iff₀ hDpos).mpr
    have h := mul_le_mul_of_nonneg_right hd (hf n).le
    rw [inv_mul_cancel₀ (hf n).ne'] at h
    simpa only [mul_comm] using h
  · exact (hC ⟨n,rfl⟩).trans (le_max_left _ _)

end
end jacobi.Analysis
