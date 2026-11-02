import jacobi.Variational.GreenWronskian

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The actual inverse diagonal is the product of the globally positive actual
homogeneous factors with unit Wronskian. Differentiating that product twice
gives its genuine C2 regularity and the exact nonlinear diagonal identity.
No diagonal ODE, factorization or Wronskian certificate is assumed.
Source: the classical Green product identity and elementary differential calculus.
Use: its classical differential identity is the analytic input to the Fredholm calibration.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual inverse Green diagonal as a function of its physical coordinate.
Use: its classical differential identity is the analytic input to the Fredholm calibration.
Article: jacobi, Theorem D.7.
-/
def L1Source.greenDiagonal (m : L1Source) (s : ℝ) (hs : 0≤s) (hp : s*observe m .top<1) (x : ℝ) : ℝ :=
  m.fredholmGreen s hs hp x x

/-- The actual Green diagonal derivative is the derivative of the two genuine homogeneous factors.
Use: computes its second derivative and the Gel'fand--Dikii polynomial without assumed smoothness.
Article: jacobi, Theorem D.7.
Proof: the proved exact Green product holds on the whole line, so its classical product derivative is the actual diagonal derivative. -/
theorem L1Source.greenDiagonal_hasDerivAt (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) (x : ℝ) :
    HasDerivAt (m.greenDiagonal s hs hp)
      (deriv (m.greenLeftSolution s hs hp) x*m.greenRightSolution s hs hp x+
        m.greenLeftSolution s hs hp x*deriv (m.greenRightSolution s hs hp) x) x := by
  have he : m.greenDiagonal s hs hp=fun y => m.greenLeftSolution s hs hp y*m.greenRightSolution s hs hp y :=
    funext fun _ => m.greenSolutions_product hs hp le_rfl
  rw [he]
  exact (m.greenLeftSolution_equation hc hs hp x).1.mul (m.greenRightSolution_equation hc hs hp x).1

/-- The actual Green diagonal has its classical second derivative everywhere.
Use: supplies the exact second-order term in the Green diagonal identity and proves C2 regularity.
Article: jacobi, Theorem D.7.
Proof: differentiate the genuine first derivative and substitute both
proved homogeneous equations. The product term is the actual Green diagonal. -/
theorem L1Source.greenDiagonal_second (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) (x : ℝ) :
    HasDerivAt (deriv (m.greenDiagonal s hs hp))
      (2*(1-2*s*m.value x)*m.greenDiagonal s hs hp x+
        2*deriv (m.greenLeftSolution s hs hp) x*deriv (m.greenRightSolution s hs hp) x) x := by
  -- Both factors and their actual derivatives are classical at every physical coordinate.
  have he : deriv (m.greenDiagonal s hs hp)=fun y =>
      deriv (m.greenLeftSolution s hs hp) y*m.greenRightSolution s hs hp y+
        m.greenLeftSolution s hs hp y*deriv (m.greenRightSolution s hs hp) y :=
    funext fun y => (m.greenDiagonal_hasDerivAt hc hs hp y).deriv
  rw [he]
  obtain ⟨hL,hL'⟩ := m.greenLeftSolution_equation hc hs hp x
  obtain ⟨hR,hR'⟩ := m.greenRightSolution_equation hc hs hp x
  convert (hL'.mul hR).add (hL.mul hR') using 1
  unfold L1Source.greenDiagonal
  rw [m.greenSolutions_product hs hp le_rfl]
  ring

/-- The actual inverse Green diagonal is twice continuously differentiable for every continuous density.
Use: verifies the exact classical regularity assumed in the Fredholm calibration equations.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: its actual first and second derivatives have been proved everywhere.
The second derivative expression is continuous by continuity of the density
and the actual factors and slopes, so the standard C2 derivative criterion applies. -/
theorem L1Source.greenDiagonal_contDiff (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) : ContDiff ℝ 2 (m.greenDiagonal s hs hp) := by
  -- The ODE provides continuity of each actual slope, including through zero.
  have hL : Continuous (m.greenLeftSolution s hs hp) := continuous_iff_continuousAt.mpr
    fun x => (m.greenLeftSolution_equation hc hs hp x).1.continuousAt
  have hR : Continuous (m.greenRightSolution s hs hp) := continuous_iff_continuousAt.mpr
    fun x => (m.greenRightSolution_equation hc hs hp x).1.continuousAt
  have hL' : Continuous (deriv (m.greenLeftSolution s hs hp)) := continuous_iff_continuousAt.mpr
    fun x => (m.greenLeftSolution_equation hc hs hp x).2.continuousAt
  have hR' : Continuous (deriv (m.greenRightSolution s hs hp)) := continuous_iff_continuousAt.mpr
    fun x => (m.greenRightSolution_equation hc hs hp x).2.continuousAt
  have hg : Continuous (m.greenDiagonal s hs hp) :=
    continuous_iff_continuousAt.mpr fun x => (m.greenDiagonal_hasDerivAt hc hs hp x).continuousAt
  change ContDiff ℝ (1+1) (m.greenDiagonal s hs hp)
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x => (m.greenDiagonal_hasDerivAt hc hs hp x).differentiableAt,by simp,?_⟩
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (m.greenDiagonal_second hc hs hp x).differentiableAt,?_⟩
  have he : deriv (deriv (m.greenDiagonal s hs hp))=fun x =>
      2*(1-2*s*m.value x)*m.greenDiagonal s hs hp x+
        2*deriv (m.greenLeftSolution s hs hp) x*deriv (m.greenRightSolution s hs hp) x :=
    funext fun x => (m.greenDiagonal_second hc hs hp x).deriv
  rw [he]
  fun_prop

/-- The actual inverse Green diagonal obeys the exact Gel'fand--Dikii identity everywhere.
Use: supplies the genuine nonlinear Green equation underlying the Fredholm optimizer calibration.
Article: jacobi, Theorem D.7.
Source: Gel'fand and Dikii, diagonal Green identity, proved here for the actual operator.
Proof: substitute the proved actual first and second derivatives and the
actual Green product. Its remaining polynomial is one minus the square
of the proved unit Wronskian, and therefore vanishes identically. -/
theorem L1Source.gelfand_dikii (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) (x : ℝ) :
    2*m.greenDiagonal s hs hp x*deriv (deriv (m.greenDiagonal s hs hp)) x-
      (deriv (m.greenDiagonal s hs hp) x)^2-
      4*(1-2*s*m.value x)*(m.greenDiagonal s hs hp x)^2+1=0 := by
  -- Every term below is an actual derivative of the actual inverse diagonal.
  rw [(m.greenDiagonal_second hc hs hp x).deriv,(m.greenDiagonal_hasDerivAt hc hs hp x).deriv]
  unfold L1Source.greenDiagonal
  rw [m.greenSolutions_product hs hp le_rfl]
  have hw := congrArg (fun r : ℝ => r^2) (m.greenSolutions_wronskian hc hs hp x)
  nlinarith [hw]

end
end jacobi.Variational
