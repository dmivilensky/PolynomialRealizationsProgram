import jacobi.Variational.GreenSolutions

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The actual globally positive homogeneous Green factors have Wronskian one.
At zero this follows from their half-line column representations and the
proved unit source jump. The homogeneous equations make the Wronskian
constant globally. Consequently the actual Green product has the precise
normalization required by the diagonal Gel'fand--Dikii identity.
Source: one-sided derivative uniqueness and the classical Wronskian identity.
Use: identifies the Wronskian constant from the actual inverse column's unit slope jump.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter jacobi.Continuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The canonical actual Green factors have their exact normalization at zero.
Use: identifies the Wronskian constant from the actual inverse column's unit slope jump.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: evaluate the two positive factor definitions and cancel the nonzero actual Green diagonal. -/
theorem L1Source.greenSolutions_zero (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) :
    m.greenRightSolution s hs hp 0=1 ∧ m.greenLeftSolution s hs hp 0=m.fredholmGreen s hs hp 0 0 := by
  simp only [L1Source.greenRightSolution,L1Source.greenLeftSolution,greenRightFactor,greenLeftFactor,
    le_refl,ite_true,div_self (m.fredholmGreen_pos hs hp 0 0).ne',and_self]

/-- The actual right factor's zero slope is the actual right Green-column slope divided by G(0,0).
Use: computes the positive Wronskian at zero from genuine derivatives.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the factor equals that column ratio on the closed right half-line.
Their classical derivatives therefore agree by one-sided derivative uniqueness. -/
theorem L1Source.greenRightSolution_deriv_zero (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) :
    deriv (m.greenRightSolution s hs hp) 0=
      m.greenBranchSlope s hs hp 0 (-1) 0/m.fredholmGreen s hs hp 0 0 := by
  -- Equality on the right half-line fixes the actual two-sided derivative at its endpoint.
  let G := m.fredholmGreen s hs hp
  have he (y : ℝ) (hy : y∈Ici (0:ℝ)) :
      m.greenRightSolution s hs hp y=m.greenBranch s hs hp 0 (-1) y/G 0 0 := by
    change greenRightFactor G y=_
    rw [greenRightFactor_column (m.fredholmGreen_pos hs hp)
      (fun hxa haz => m.fredholmGreen_markov hs hp hxa haz) le_rfl hy,
      m.greenBranch_right hs hp hy]
  have hb := ((m.greenBranch_hasDerivAt hs hp 0 (-1) 0).div_const (G 0 0)).hasDerivWithinAt (s := Ici (0:ℝ))
  have hnew := hb.congr he (he 0 (by simp))
  have hactual := (m.greenRightSolution_equation hc hs hp 0).1.hasDerivWithinAt (s := Ici (0:ℝ))
  exact (hactual.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (hnew.derivWithin (uniqueDiffWithinAt_Ici 0))

/-- The actual left factor's zero slope is the actual left Green-column slope.
Use: together with the right slope, identifies the Wronskian constant as exactly one.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: reflection symmetry of the actual kernel identifies the left factor
with its zero-source left column on the closed left half-line. Uniqueness
of the one-sided derivative then gives the actual global derivative. -/
theorem L1Source.greenLeftSolution_deriv_zero (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) :
    deriv (m.greenLeftSolution s hs hp) 0=m.greenBranchSlope s hs hp 0 1 0 := by
  -- The source-point corner belongs to the Green column, while the factor is globally smooth.
  let G := m.fredholmGreen s hs hp
  have he (y : ℝ) (hy : y∈Iic (0:ℝ)) :
      m.greenLeftSolution s hs hp y=m.greenBranch s hs hp 0 1 y := by
    change y≤0 at hy
    change greenLeftFactor G y=_
    rw [greenLeftFactor,ite_eq_left hy,m.greenBranch_left hs hp hy,
      m.fredholmGreen_symm hs hp 0 y]
  have hb := (m.greenBranch_hasDerivAt hs hp 0 1 0).hasDerivWithinAt (s := Iic (0:ℝ))
  have hnew := hb.congr he (he 0 (by simp))
  have hactual := (m.greenLeftSolution_equation hc hs hp 0).1.hasDerivWithinAt (s := Iic (0:ℝ))
  exact (hactual.derivWithin (uniqueDiffWithinAt_Iic 0)).symm.trans
    (hnew.derivWithin (uniqueDiffWithinAt_Iic 0))

/-- The actual positive homogeneous Green factors have precisely unit Wronskian everywhere.
Use: gives the normalization and positive constant in the full Green product and diagonal identities.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the homogeneous equations make the Wronskian derivative zero. At
zero the canonical factor values and the proved one-sided column slopes
reduce its value to the actual Green source jump, already proved one. -/
theorem L1Source.greenSolutions_wronskian (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) (x : ℝ) :
    m.greenRightSolution s hs hp x*deriv (m.greenLeftSolution s hs hp) x-
      deriv (m.greenRightSolution s hs hp) x*m.greenLeftSolution s hs hp x=1 := by
  -- Differentiate actual globally constructed functions, not formal ODE data.
  let R := m.greenRightSolution s hs hp
  let L := m.greenLeftSolution s hs hp
  let W (y : ℝ) := R y*deriv L y-deriv R y*L y
  have hW (y : ℝ) : HasDerivAt W 0 y := by
    obtain ⟨hR,hR'⟩ := m.greenRightSolution_equation hc hs hp y
    obtain ⟨hL,hL'⟩ := m.greenLeftSolution_equation hc hs hp y
    convert (hR.mul hL').sub (hR'.mul hL) using 1
    ring
  have hconst : W x=W 0 := is_const_of_deriv_eq_zero (fun y => (hW y).differentiableAt)
    (fun y => (hW y).deriv) x 0
  have hdiag : m.fredholmGreen s hs hp 0 0≠0 := (m.fredholmGreen_pos hs hp 0 0).ne'
  have hz : W 0=1 := by
    dsimp only [W,R,L]
    rw [(m.greenSolutions_zero hs hp).1,(m.greenSolutions_zero hs hp).2,
      m.greenRightSolution_deriv_zero hc hs hp,m.greenLeftSolution_deriv_zero hc hs hp,
      one_mul,div_mul_cancel₀ _ hdiag,m.greenBranch_jump hs hp]
  exact hconst.trans hz

end
end jacobi.Variational
