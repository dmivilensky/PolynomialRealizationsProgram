import krylov.Methods.QuadraticConsistency
import krylov.Reference.Stopping

set_option autoImplicit false
/-!
Article: main_krylov, lem:U and apB:lem:filtration, actual raw quadratic search domains.
Use: derive strict positivity of the real raw-method probe curvature and
actual exact line length from global CG consistency at every genuinely
nonzero quadratic reference gradient, independently of its chosen direction
normalization and finite correction protocol.
Source: the proved actual quadratic transcript, positive true CG line
invariant and genuine exact-search direction-scale cancellation.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual globally CG-consistent raw method has strictly positive genuine reference probe curvature and line length at every true nonzero quadratic gradient.
Use: Every actual globally CG-consistent raw method has strictly positive genuine reference probe curvature and line length at every true nonzero quadratic gradient.
Article: main_krylov, lem:U and apB:lem:filtration, actual raw quadratic search domains.
Proof: The true current nonzero residual certifies its actual earlier prefix. Raw consistency supplies a positive multiple of the real CG direction; the genuine positive CG curvature scales quadratically and the actual exact line length scales reciprocally. -/
theorem quadratic_search_positive (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : CG.gradient Q g k≠0) :
    let H := methodRun m (fun _ => Q) (fun _ => Q) g k
    0 < inner ℝ (m.direction H) (Q (m.direction H)) ∧
      0 < lineLength H.gradient (m.direction H) (Q (m.direction H)) := by
  -- Derive both true search-domain quantities from this actual raw quadratic history and its real positive CG direction scale.
  let H := methodRun m (fun _ => Q) (fun _ => Q) g k
  obtain ⟨c,hc,hdir,_⟩ := hm Q hQ hpos g k
  have hpre : ∀ i < k, CG.gradient Q g i≠0 := by
    intro i hi hz
    exact hg (CG.gradient_eq_zero_of_le Q g hz hi.le)
  have hCG := CG.invariant_line_pos Q hpos g k (CG.invariant Q hQ hpos g k hpre) hg
  have hC := hpos _ hCG.1
  constructor
  · rw [hdir,map_smul,real_inner_smul_left,real_inner_smul_right]
    exact mul_pos hc (mul_pos hc hC)
  · rw [quadratic_gradient_eq_cg m hm Q hQ hpos g k,hdir,map_smul,lineLength_smul _ _ _ hc.ne']
    exact div_pos hCG.2.1 hc
end
end krylov.Methods
