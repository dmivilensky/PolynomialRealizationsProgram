import jacobi.Variational.GreenDiagonal
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The two actual positive homogeneous solutions decay at their respective
ends. Their positive ratios have zero endpoint limits by the uniform lower
Green diagonal bound, and their derivatives are the reciprocal squares
fixed by the unit Wronskian. These identities provide the exact half-line
integrals needed to identify the spatial determinant integral.
Source: the actual Wronskian, H1 endpoint limits and the improper FTC.
Use: fixes the integration constants in the reciprocal-square Green identities.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual homogeneous-solution ratios vanish at the opposite decay endpoints.
Use: fixes the integration constants in the reciprocal-square Green identities.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: g=phi_-*phi_+>=1/2 implies phiMinus / phiPlus<=2phi_-²
and its reflected counterpart. The actual decaying factors and the squeeze theorem give both limits. -/
theorem L1Source.greenSolution_ratio_limits (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) :
    Tendsto (fun x => m.greenLeftSolution s hs hp x/m.greenRightSolution s hs hp x) atBot (𝓝 0) ∧
      Tendsto (fun x => m.greenRightSolution s hs hp x/m.greenLeftSolution s hs hp x) atTop (𝓝 0) := by
  -- Uniform positivity of the actual inverse diagonal controls both quotient endpoints.
  let L := m.greenLeftSolution s hs hp
  let R := m.greenRightSolution s hs hp
  have hb (x : ℝ) : L x/R x≤2*L x^2 ∧ R x/L x≤2*R x^2 := by
    obtain ⟨hR,hL⟩ := m.greenSolutions_pos hs hp x
    have hg := (m.fredholmGreen_diagonal hs hp x).1
    rw [m.greenSolutions_product hs hp le_rfl] at hg
    constructor
    · apply (div_le_iff₀ hR).mpr
      have hh := mul_le_mul_of_nonneg_left hg hL.le
      dsimp only [L,R]
      nlinarith
    · apply (div_le_iff₀ hL).mpr
      have hh := mul_le_mul_of_nonneg_left hg hR.le
      dsimp only [L,R]
      nlinarith
  constructor
  · apply squeeze_zero (fun x => div_nonneg (m.greenSolutions_pos hs hp x).2.le (m.greenSolutions_pos hs hp x).1.le)
      (fun x => (hb x).1)
    simpa only [zero_pow (by decide : 2≠0),mul_zero] using ((m.greenLeftSolution_limit hs hp).pow 2).const_mul 2
  · apply squeeze_zero (fun x => div_nonneg (m.greenSolutions_pos hs hp x).1.le (m.greenSolutions_pos hs hp x).2.le)
      (fun x => (hb x).2)
    simpa only [zero_pow (by decide : 2≠0),mul_zero] using ((m.greenRightSolution_limit hs hp).pow 2).const_mul 2

/-- The actual positive Green solution ratios have the reciprocal-square derivatives fixed by their unit Wronskian.
Use: evaluates the kernel-square to diagonal-square integral by the whole-line FTC.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: apply the quotient rule to the actual solutions and replace its
numerator by the already proved actual unit Wronskian. -/
theorem L1Source.greenSolution_ratio_derivatives (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) (x : ℝ) :
    HasDerivAt (fun y => m.greenLeftSolution s hs hp y/m.greenRightSolution s hs hp y)
      (1/(m.greenRightSolution s hs hp x)^2) x ∧
    HasDerivAt (fun y => -m.greenRightSolution s hs hp y/m.greenLeftSolution s hs hp y)
      (1/(m.greenLeftSolution s hs hp x)^2) x := by
  -- The quotient numerators are the same genuine Wronskian, in the two orientations.
  obtain ⟨hR,hL⟩ := m.greenSolutions_pos hs hp x
  obtain ⟨hdR,_⟩ := m.greenRightSolution_equation hc hs hp x
  obtain ⟨hdL,_⟩ := m.greenLeftSolution_equation hc hs hp x
  have hw := m.greenSolutions_wronskian hc hs hp x
  constructor
  · convert hdL.div hdR hR.ne' using 1
    congr 1
    nlinarith
  · convert hdR.neg.div hdL hL.ne' using 1
    congr 1
    dsimp only [Pi.neg_apply]
    nlinarith

end
end jacobi.Variational
