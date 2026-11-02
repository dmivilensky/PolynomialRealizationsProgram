import jacobi.Variational.GreenColumns
import jacobi.Continuum.GreenFactors
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The actual positive Green kernel determines global left and right factors.
Their local fixed-column representations give the classical differential
equation everywhere for continuous densities. All positivity and interval
factorization assumptions are discharged by the actual subcritical inverse.
Source: the proved Green interval factorization and local classical column equations.
Use: discharges all denominator and positivity conditions of the global homogeneous Green factors.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter jacobi.Continuum
open chebyshev2.Sobolev
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every entry of the actual subcritical Green kernel is strictly positive.
Use: discharges all denominator and positivity conditions of the global homogeneous Green factors.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: its proved free exponential lower bound is strictly positive. -/
theorem L1Source.fredholmGreen_pos (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x y : ℝ) : 0<m.fredholmGreen s hs hp x y := by
  have h := m.fredholmGreen_lower hs hp x y
  nlinarith [exp_pos (-|x-y|)]

/-- The actual globally positive right Green solution, normalized to one at zero.
Use: its actual differential equation and left partner give the Green product and diagonal identities.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def L1Source.greenRightSolution (m : L1Source) (s : ℝ) (hs : 0≤s) (hp : s*observe m .top<1) : ℝ → ℝ :=
  greenRightFactor (m.fredholmGreen s hs hp)

/-- The actual globally positive left Green solution, normalized by G(0,0).
Use: the two actual solutions have unit positive Wronskian and reconstruct the inverse kernel.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def L1Source.greenLeftSolution (m : L1Source) (s : ℝ) (hs : 0≤s) (hp : s*observe m .top<1) : ℝ → ℝ :=
  greenLeftFactor (m.fredholmGreen s hs hp)

/-- Both global homogeneous Green solutions are strictly positive everywhere.
Use: licenses their logarithmic derivatives and fixes the positive Wronskian branch.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: apply the algebraic factor positivity to the actual strictly positive inverse kernel. -/
theorem L1Source.greenSolutions_pos (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (x : ℝ) :
    0<m.greenRightSolution s hs hp x ∧ 0<m.greenLeftSolution s hs hp x :=
  greenFactors_pos (m.fredholmGreen_pos hs hp) x

/-- The actual ordered inverse kernel is the product of its two genuine globally positive solutions.
Use: identifies the diagonal with their product before proving its differential identity.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: use the proved actual interval factorization in the general positive factor construction. -/
theorem L1Source.greenSolutions_product (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) {x y : ℝ} (hxy : x≤y) :
    m.fredholmGreen s hs hp x y=m.greenLeftSolution s hs hp x*m.greenRightSolution s hs hp y :=
  greenFactors_product (m.fredholmGreen_pos hs hp) (fun hxa haz => m.fredholmGreen_markov hs hp hxa haz) hxy

/-- A local classical model transfers its differential equation to the actual function and its actual derivative.
Use: glues fixed-column Green representations into genuine global homogeneous solutions.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: local equality transfers the first derivative, and its germ equality
also transfers the derivative function. The second model derivative then
becomes the actual second derivative with the same potential coefficient. -/
theorem ode_from_local_model {f g e : ℝ → ℝ} {V : ℝ → ℝ} {x : ℝ}
    (hfg : f=ᶠ[𝓝 x] g) (hg : ∀ y,HasDerivAt g (e y) y)
    (he : HasDerivAt e (V x*g x) x) :
    HasDerivAt f (deriv f x) x ∧ HasDerivAt (deriv f) (V x*f x) x := by
  -- Derivative equality is proved on a whole germ before differentiating again.
  have hf := (hg x).congr_of_eventuallyEq hfg
  have hder : deriv f=ᶠ[𝓝 x] e := hfg.deriv.trans (Eventually.of_forall fun y => (hg y).deriv)
  refine ⟨by rwa [hf.deriv],?_⟩
  have h := he.congr_of_eventuallyEq hder
  rwa [← hfg.eq_of_nhds] at h

/-- The actual right Green factor solves the homogeneous Schrodinger equation classically everywhere.
Use: constructs phi_+ without assuming a Jost solution or a differential-equation certificate.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: move a column source strictly left of the point and zero. The actual
right factor equals that smooth right exponential extension divided by a
positive fixed kernel value throughout a neighborhood. Transfer both derivatives. -/
theorem L1Source.greenRightSolution_equation (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) (x : ℝ) :
    HasDerivAt (m.greenRightSolution s hs hp) (deriv (m.greenRightSolution s hs hp) x) x ∧
      HasDerivAt (deriv (m.greenRightSolution s hs hp))
        ((1-2*s*m.value x)*m.greenRightSolution s hs hp x) x := by
  -- The source stays strictly outside a full neighborhood of the evaluation point.
  let a := min (0:ℝ) x-1
  have ha0 : a<0 := by dsimp only [a]; linarith [min_le_left (0:ℝ) x]
  have hax : a<x := by dsimp only [a]; linarith [min_le_right (0:ℝ) x]
  let G := m.fredholmGreen s hs hp
  let g (y : ℝ) := m.greenBranch s hs hp a (-1) y/G a 0
  let e (y : ℝ) := m.greenBranchSlope s hs hp a (-1) y/G a 0
  have hlocal : m.greenRightSolution s hs hp=ᶠ[𝓝 x] g := by
    filter_upwards [Ioi_mem_nhds hax] with y hy
    change greenRightFactor G y=m.greenBranch s hs hp a (-1) y/G a 0
    rw [greenRightFactor_column (m.fredholmGreen_pos hs hp)
      (fun hxa haz => m.fredholmGreen_markov hs hp hxa haz) ha0.le hy.le,
      m.greenBranch_right hs hp hy.le]
  have hg (y : ℝ) : HasDerivAt g (e y) y := (m.greenBranch_hasDerivAt hs hp a (-1) y).div_const (G a 0)
  have he : HasDerivAt e ((1-2*s*m.value x)*g x) x := by
    convert (m.greenBranch_second hc hs hp a (-1) x (by norm_num)).div_const (G a 0) using 1
    dsimp only [g]
    rw [m.greenBranch_right hs hp hax.le]
    unfold L1Source.greenColumnSource
    ring
  exact ode_from_local_model (V := fun y => 1-2*s*m.value y) hlocal hg he

/-- The actual left Green factor solves the homogeneous Schrodinger equation classically everywhere.
Use: constructs phi_- and the two actual factors needed for the Green diagonal identity.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: move the column source strictly right of the point and zero. The
left factor is a positive fixed multiple of the smooth left branch on a
neighborhood. Symmetry identifies the column variables; transfer both derivatives. -/
theorem L1Source.greenLeftSolution_equation (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) (x : ℝ) :
    HasDerivAt (m.greenLeftSolution s hs hp) (deriv (m.greenLeftSolution s hs hp) x) x ∧
      HasDerivAt (deriv (m.greenLeftSolution s hs hp))
        ((1-2*s*m.value x)*m.greenLeftSolution s hs hp x) x := by
  -- The source is strictly beyond both zero and the point in a whole neighborhood.
  let b := max (0:ℝ) x+1
  have hb0 : 0<b := by dsimp only [b]; linarith [le_max_left (0:ℝ) x]
  have hxb : x<b := by dsimp only [b]; linarith [le_max_right (0:ℝ) x]
  let G := m.fredholmGreen s hs hp
  let c := G 0 0/G 0 b
  let g (y : ℝ) := c*m.greenBranch s hs hp b 1 y
  let e (y : ℝ) := c*m.greenBranchSlope s hs hp b 1 y
  have hlocal : m.greenLeftSolution s hs hp=ᶠ[𝓝 x] g := by
    filter_upwards [Iio_mem_nhds hxb] with y hy
    change greenLeftFactor G y=c*m.greenBranch s hs hp b 1 y
    rw [greenLeftFactor_column (m.fredholmGreen_pos hs hp)
      (fun hxa haz => m.fredholmGreen_markov hs hp hxa haz) hb0.le hy.le,
      m.greenBranch_left hs hp hy.le,m.fredholmGreen_symm hs hp b y]
    dsimp only [c,G]
    ring
  have hg (y : ℝ) : HasDerivAt g (e y) y := (m.greenBranch_hasDerivAt hs hp b 1 y).const_mul c
  have he : HasDerivAt e ((1-2*s*m.value x)*g x) x := by
    convert (m.greenBranch_second hc hs hp b 1 x (by norm_num)).const_mul c using 1
    dsimp only [g]
    rw [m.greenBranch_left hs hp hxb.le]
    unfold L1Source.greenColumnSource
    ring
  exact ode_from_local_model (V := fun y => 1-2*s*m.value y) hlocal hg he

/-- The actual right Green solution decays to zero at the positive end.
Use: gives the zero ratio endpoint in the Green reciprocal-diagonal integral identity.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: on the right half-line it is the actual zero-source H1 Green representative
at that point, divided by its fixed positive diagonal normalization. -/
theorem L1Source.greenRightSolution_limit (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) : Tendsto (m.greenRightSolution s hs hp) atTop (𝓝 0) := by
  -- The endpoint condition is inherited from an actual H1 vector, rather than assumed for the solution.
  let G := m.fredholmGreen s hs hp
  have h := (H1.rep_tendsto_zero (m.fredholmGreenVector s hs hp 0)).1.div_const (G 0 0)
  simp only [zero_div,m.fredholmGreenVector_rep hs hp] at h
  have he : m.greenRightSolution s hs hp=ᶠ[atTop] fun x => G 0 x/G 0 0 := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    exact greenRightFactor_column (m.fredholmGreen_pos hs hp)
      (fun hxa haz => m.fredholmGreen_markov hs hp hxa haz) le_rfl hx
  exact h.congr' he.symm

/-- The actual left Green solution decays to zero at the negative end.
Use: fixes the left zero ratio endpoint and identifies the actual left-decaying branch.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: its left half-line is the zero-source actual H1 Green column; its
negative-end decay follows from the proved H1 representative endpoint theorem. -/
theorem L1Source.greenLeftSolution_limit (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) : Tendsto (m.greenLeftSolution s hs hp) atBot (𝓝 0) := by
  -- Kernel symmetry identifies the actual H1 column with the selected left factor.
  have h := (H1.rep_tendsto_zero (m.fredholmGreenVector s hs hp 0)).2
  have hr : H1.rep (m.fredholmGreenVector s hs hp 0)=fun x => m.fredholmGreen s hs hp 0 x :=
    funext fun x => m.fredholmGreenVector_rep hs hp 0 x
  rw [hr] at h
  have he : m.greenLeftSolution s hs hp=ᶠ[atBot] fun x => m.fredholmGreen s hs hp 0 x := by
    filter_upwards [eventually_le_atBot (0:ℝ)] with x hx
    change greenLeftFactor (m.fredholmGreen s hs hp) x=_
    rw [greenLeftFactor,ite_eq_left hx,m.fredholmGreen_symm hs hp x 0]
  exact h.congr' he.symm

end
end jacobi.Variational
