import krylov.Completion.ActionEndpoints
import Mathlib.Topology.Order.IntermediateValue
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, complete full-action curvature range.
Use: prove that every curvature between the actual physical full-action
extrema is attained, including coincident and singular endpoints.
Source: the proved Loewner extrema and an affine segment of feasible matrices;
the scalar intermediate-value theorem is from mathlib.
-/

namespace krylov.Completion
noncomputable section
open Matrix
variable {n p : ℕ}

/-- The full-action physical curvature range is exactly the closed interval
between the constructed actual lower and upper endpoint curvatures.
Use: the source's additional full-action constraint retains an attained closed
interval, including the collapsed case; endpoint realization is not assumed.
Article: main_krylov, thm:radau, full-action range.
Proof: the actual shorted-form endpoints are feasible Loewner extrema. Every
intermediate curvature is realized on their affine segment; positivity and
the entire observed action are preserved by the same convex combination. -/
theorem full_action_curvature_range
    (A : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (mu L c : ℝ) (hlo : (A-mu • 1).PosSemidef) (hhi : (L • 1-A).PosSemidef) :
    (∃ C : Matrix (Fin n) (Fin n) ℝ,
      (C-mu • 1).PosSemidef ∧ (L • 1-C).PosSemidef ∧ C*S=A*S ∧ d ⬝ᵥ (C*ᵥ d)=c) ↔
      d ⬝ᵥ (lowerActionEndpoint A mu hlo S*ᵥ d)≤c ∧
        c≤d ⬝ᵥ (upperActionEndpoint A L hhi S*ᵥ d) := by
  let Alo := lowerActionEndpoint A mu hlo S
  let Ahi := upperActionEndpoint A L hhi S
  obtain ⟨hll,hlh,hls,hhl,hhh,hhs⟩ := full_action_endpoint_feasibility A S mu L hlo hhi
  constructor
  · rintro ⟨C,hCl,hCh,hCs,rfl⟩
    obtain ⟨hbelow,habove⟩ := full_action_endpoint_extrema A C S mu L hlo hhi hCl hCh hCs
    have hl := hbelow.dotProduct_mulVec_nonneg d
    have hh := habove.dotProduct_mulVec_nonneg d
    simp only [star_trivial,sub_mulVec,dotProduct_sub] at hl hh
    exact ⟨by linarith,by linarith⟩
  · intro hc
    let cl := d ⬝ᵥ (Alo*ᵥ d)
    let ch := d ⬝ᵥ (Ahi*ᵥ d)
    let f := fun t : ℝ => (1-t)*cl+t*ch
    have hf : ContinuousOn f (Set.Icc 0 1) := by fun_prop
    have hcf : c∈Set.Icc (f 0) (f 1) := by simpa only [Set.mem_Icc,f,sub_zero,one_mul,zero_mul,add_zero,
      sub_self,zero_add] using hc
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ)≤1) hf hcf
    let C := (1-t) • Alo+t • Ahi
    have htl : 0≤1-t := sub_nonneg.mpr ht.2
    have hlower : C-mu • 1=(1-t) • (Alo-mu • 1)+t • (Ahi-mu • 1) := by
      dsimp only [C]
      module
    have hupper : L • 1-C=(1-t) • (L • 1-Alo)+t • (L • 1-Ahi) := by
      dsimp only [C]
      module
    refine ⟨C,?_,?_,?_,?_⟩
    · rw [hlower]
      exact (hll.smul htl).add (hhl.smul ht.1)
    · rw [hupper]
      exact (hlh.smul htl).add (hhh.smul ht.1)
    · change ((1-t) • Alo+t • Ahi)*S=A*S
      rw [Matrix.add_mul,Matrix.smul_mul,Matrix.smul_mul,hls,hhs]
      module
    · change d ⬝ᵥ (((1-t) • Alo+t • Ahi)*ᵥ d)=c
      simp only [add_mulVec,smul_mulVec,dotProduct_add,dotProduct_smul,smul_eq_mul]
      exact he

end
end krylov.Completion
