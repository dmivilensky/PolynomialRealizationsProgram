import krylov.OneGradient.HiddenPlaneLeading
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), genuine opposite hidden endpoint budgets.
Use: the actual four-adversary construction uses both real hidden
completions of the centre and of its opposite, in the original norm ball.
Source: complete closed-disc hidden-entry completion and exact planar
linearity, with symmetry and all singular endpoints retained.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Both actual centre-plus/minus-hidden matrices are genuine spectral
contractions on the physical plane, including the disc boundary.
Use: the four actual signed lower scenarios satisfy exact source budgets.
Article: main_krylov, thm:local(c), genuine hidden endpoint budgets.
Proof: planar linearity identifies the actual sums and differences with
the already proved true closed Schur interval endpoints. -/
theorem hiddenPlane_endpoint_norms
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (a g : ℝ) (hd : a^2+g^2≤1) :
    let S := planarMatrix e h (hiddenPlaneCentre a g) a g
    let H := planarMatrix e h (hiddenPlaneHalfWidth a g) 0 0
    ‖S+H‖≤1 ∧ ‖S-H‖≤1 := by
  have hp := hiddenPlane_completion_bound e h he hh heh a g 1 hd (by norm_num)
  have hm := hiddenPlane_completion_bound e h he hh heh a g (-1) hd (by norm_num)
  have heqp : planarMatrix e h (hiddenPlaneCentre a g+hiddenPlaneHalfWidth a g) a g=
      planarMatrix e h (hiddenPlaneCentre a g) a g+planarMatrix e h (hiddenPlaneHalfWidth a g) 0 0 := by
    unfold planarMatrix
    module
  have heqm : planarMatrix e h (hiddenPlaneCentre a g-hiddenPlaneHalfWidth a g) a g=
      planarMatrix e h (hiddenPlaneCentre a g) a g-planarMatrix e h (hiddenPlaneHalfWidth a g) 0 0 := by
    unfold planarMatrix
    module
  simp only [one_mul,heqp] at hp
  simp only [neg_one_mul,← sub_eq_add_neg,heqm] at hm
  exact ⟨hp,hm⟩

end
end krylov.OneGradient
