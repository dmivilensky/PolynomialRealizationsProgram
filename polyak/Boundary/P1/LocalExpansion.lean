import polyak.Boundary.P1.LocalImplicit

/-!
Article: Appendix C, the one-atom endpoint expansion before inversion to q.
Use: derive the cubic coefficient from the actual regular source equations.
-/

namespace polyak.Boundary.P1
noncomputable section
open Filter
open scoped Topology

/-- Article: the exact polynomial remainder after the linear part of the first contact equation. -/
def equationRemainder (z A B : ℝ) : ℝ :=
  B+2*A^2+2*B^2-2*z*B^2-2*z^4*B^3+
    2*z*uLinear z A*(B-z*B^2-z^4*B^3)-z^3*B^2-
      gapLinear z A B*contactQuadratic z B

theorem regularEquation0_expansion (z A B : ℝ) :
    regularEquation0 z A B=4*A-1/2+z+z^2*equationRemainder z A B := by
  unfold regularEquation0 equationRemainder uLinear gapLinear atomProductLinear contactQuadratic
  ring

theorem localBranch_coordinate_analyticAt (i : Fin 2) :
    AnalyticAt ℝ (fun z => localBranch z i) 0 :=
  ((ContinuousLinearMap.proj i : Coordinates →L[ℝ] ℝ).analyticAt (localBranch 0)).comp
    localBranch_analyticAt

/-- Article: the first unknown has the exact derivative A′(0)=−1/4. -/
theorem localBranch_A_hasDerivAt : HasDerivAt (fun z => localBranch z 0) (-1/4) 0 := by
  let R : ℝ → ℝ := fun z => equationRemainder z (localBranch z 0) (localBranch z 1)
  have hA := localBranch_coordinate_analyticAt 0
  have hB := localBranch_coordinate_analyticAt 1
  have hR : AnalyticAt ℝ R 0 := by
    dsimp only [R,equationRemainder,uLinear,gapLinear,contactQuadratic]
    fun_prop
  have hz : HasDerivAt (fun z : ℝ => z^2) 0 0 := by
    convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1
    · funext z
      rfl
    · norm_num
  have hr : HasDerivAt (fun z : ℝ => z^2*R z/4) 0 0 := by
    simpa using (hz.mul hR.differentiableAt.hasDerivAt).div_const 4
  have hlinear : HasDerivAt (fun z : ℝ => 1/8-z/4-z^2*R z/4) (-1/4) 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (1/8 : ℝ)).sub
      ((hasDerivAt_id (0 : ℝ)).div_const 4)).sub hr using 1
    · funext z
      rfl
    · norm_num
  apply hlinear.congr_of_eventuallyEq
  filter_upwards [localBranch_equations] with z hz
  have he := congrFun hz 0
  change regularEquation0 z (localBranch z 0) (localBranch z 1)=0 at he
  rw [regularEquation0_expansion] at he
  dsimp only [R]
  linarith

/-- Article: u₁ along the actual analytic implicit source branch. -/
def localU (z : ℝ) : ℝ := branchU z (localBranch z 0)

/-- Article: the complete printed one-atom expansion with O(z⁴), on both sides of zero. -/
theorem localU_expansion :
    (fun z : ℝ => localU z-(1-z/2+z^2/8-z^3/4))=O[𝓝 0] (fun z => z^4) := by
  have h := Asymptotics.analytic_first_order (localBranch_coordinate_analyticAt 0)
    localBranch_A_hasDerivAt
  have hh := h.mul (Asymptotics.isBigO_refl (fun z : ℝ => z^2) (𝓝 0))
  convert hh using 1
  · funext z
    rw [localBranch_initial.1]
    unfold localU branchU
    ring
  · funext z
    ring

/-- Article: the compactified one-atom endpoint has u₁→1. -/
theorem localU_tendsto : Tendsto localU (𝓝 (0 : ℝ)) (𝓝 1) := by
  have hA := (localBranch_coordinate_analyticAt 0).continuousAt
  have hc : ContinuousAt localU 0 := by
    unfold localU branchU
    fun_prop
  simpa [localU,branchU] using hc.tendsto

end
end polyak.Boundary.P1
