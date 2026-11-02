import jacobi.Oscillation.PhaseIntegral

/-!
Article: jacobi, Proposition B.1.
The constructed literal phase integral rotates the original normalized
state exactly. Constancy of two explicitly differentiated rotation
invariants proves the representation, so no continuous angle lift or
phase/zero correspondence is an additional assumption.
Use: its proved zero derivative identifies the genuine continuous phase with the original solution.
-/
namespace jacobi.Oscillation.RestoringSolution
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {I : Set ℝ} (S : RestoringSolution I)

/-- The actual normalized state rotated backwards by its constructed phase, first coordinate.
Use: its proved zero derivative identifies the genuine continuous phase with the original solution.
Article: jacobi, Proposition B.1.
-/
def rotatedCos (base x : ℝ) : ℝ :=
  S.unitCos x*cos (S.phase base x)+S.unitSin x*sin (S.phase base x)

/-- The actual normalized state rotated backwards by its constructed phase, second coordinate.
Use: the second constant coordinate removes any unsupported choice of angle branch.
Article: jacobi, Proposition B.1.
-/
def rotatedSin (base x : ℝ) : ℝ :=
  S.unitSin x*cos (S.phase base x)-S.unitCos x*sin (S.phase base x)

/-- Both original normalized-state rotation invariants have genuine zero ordinary derivatives.
Use: proves the actual continuous phase representation on the full physical interval.
Article: jacobi, Proposition B.1.
Proof: differentiate the genuine phase integral and the original normalized
state coordinates. Their proved rotating-frame equations cancel the four
terms in each invariant derivative exactly. -/
theorem rotated_hasDerivAt (hI : Convex ℝ I) {base x : ℝ} (hb : base∈I) (hx : x∈I) :
    HasDerivAt (S.rotatedCos base) 0 x ∧ HasDerivAt (S.rotatedSin base) 0 x := by
  -- All derivatives here come from the original state and the actual convergent phase integral.
  have ht := S.phase_hasDerivAt hI hb hx
  have hC := S.unitCos_hasDerivAt hx
  have hS := S.unitSin_hasDerivAt hx
  constructor
  · convert (hC.mul ht.cos).add (hS.mul ht.sin) using 1
    · rfl
    · ring
  · convert (hS.mul ht.cos).sub (hC.mul ht.sin) using 1
    · rfl
    · ring

/-- Both original rotation invariants equal the original normalized state at the actual phase base point.
Use: fixes the exact phase normalization without a free analytic or integer-valued phase constant.
Article: jacobi, Proposition B.1.
Proof: both actual derivatives vanish on the open connected comparison
interval. The community constancy theorem identifies their values with
the base point, where the genuine phase integral is exactly zero. -/
theorem rotated_eq (hIo : IsOpen I) (hI : Convex ℝ I) {base x : ℝ} (hb : base∈I) (hx : x∈I) :
    S.rotatedCos base x=S.unitCos base ∧ S.rotatedSin base x=S.unitSin base := by
  -- Connectedness is applied only after proving actual zero derivatives, not as a phase-lifting premise.
  have hC := hIo.is_const_of_deriv_eq_zero hI.isPreconnected
    (fun t ht => ((S.rotated_hasDerivAt hI hb ht).1).differentiableAt.differentiableWithinAt)
    (fun t ht => ((S.rotated_hasDerivAt hI hb ht).1).deriv) hx hb
  have hS := hIo.is_const_of_deriv_eq_zero hI.isPreconnected
    (fun t ht => ((S.rotated_hasDerivAt hI hb ht).2).differentiableAt.differentiableWithinAt)
    (fun t ht => ((S.rotated_hasDerivAt hI hb ht).2).deriv) hx hb
  simpa only [rotatedCos,rotatedSin,S.phase_self,sin_zero,cos_zero,mul_one,mul_zero,
    add_zero,sub_zero] using And.intro hC hS

/-- The actual normalized original state has exactly the sine/cosine representation of its genuinely constructed continuous phase.
Use: identifies every original solution zero with an actual phase level and supports the quantitative phase integral estimates.
Article: jacobi, Proposition B.1.
Proof: solve the two proved constant rotation identities. The actual
sine/cosine square identity inverts that literal rotation matrix exactly. -/
theorem phase_representation (hIo : IsOpen I) (hI : Convex ℝ I) {base x : ℝ}
    (hb : base∈I) (hx : x∈I) :
    S.unitCos x=S.unitCos base*cos (S.phase base x)-S.unitSin base*sin (S.phase base x) ∧
    S.unitSin x=S.unitSin base*cos (S.phase base x)+S.unitCos base*sin (S.phase base x) := by
  obtain ⟨hC,hS⟩ := S.rotated_eq hIo hI hb hx
  unfold rotatedCos at hC
  unfold rotatedSin at hS
  have ht := Real.sin_sq_add_cos_sq (S.phase base x)
  constructor
  · linear_combination cos (S.phase base x)*hC-sin (S.phase base x)*hS-S.unitCos x*ht
  · linear_combination sin (S.phase base x)*hC+cos (S.phase base x)*hS-S.unitSin x*ht

end
end jacobi.Oscillation.RestoringSolution
