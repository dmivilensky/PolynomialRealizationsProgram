import jacobi.GelfandLevitan.TransformedSecondSmoothness
import jacobi.GelfandLevitan.MidpointDiagonalZero

/-!
Article: jacobi, Theorem 2.1.
The target potential uses the genuine derivative of the original diagonal,
independently of a choice of positive strip. Its symmetric extension is
continuous across the physical midpoint and agrees with every actual
strip coefficient wherever that strip is a relative neighborhood.
Use: diagonalPhysicalSlope and the improper-mean FTC use the same genuine w, including both proved zero boundary values.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original diagonal as a real physical-coordinate function.
Use: diagonalPhysicalSlope and the improper-mean FTC use the same genuine w, including both proved zero boundary values.
Article: jacobi, Theorem 2.1.
-/
def diagonalPhysical (a : ℝ) (ha : -1<a) (t : ℝ) : ℝ :=
  kernelDiagonal a ha (halfParameterClamp t)

/-- The actual one-sided derivative of w on its original positive half domain.
Use: halfTargetPotential defines the strip-independent original q+2*w', retaining the left derivative at the midpoint.
Article: jacobi, Theorem 2.1.
-/
def diagonalPhysicalSlope (a : ℝ) (ha : -1<a) : ℝ → ℝ :=
  derivWithin (diagonalPhysical a ha) (Ioc (0:ℝ) (1/2))

/-- The original physical half-domain target coefficient, with its genuine derivative.
Use: targetPotential extends this actual coefficient by physical reflection, and the full reflected waves satisfy its differential equation.
Article: jacobi, Theorem 2.1.
-/
def halfTargetPotential (a : ℝ) (ha : -1<a) (t : ℝ) : ℝ :=
  potential a t+2*diagonalPhysicalSlope a ha t

/-- The genuine symmetric extension of the original transformed potential.
Use: full target eigenfunctions and the differential action of H_alpha use this same continuous potential on (0,1).
Article: jacobi, Proposition 2.2.
-/
def targetPotential (a : ℝ) (ha : -1<a) (t : ℝ) : ℝ :=
  halfTargetPotential a ha (min t (1-t))

/-- The genuine original diagonal derivative is continuous on its whole positive half domain.
Use: targetPotential_continuousOn proves actual midpoint continuity of the reflected potential.
Article: jacobi, Proposition 2.2.
Proof: the independently proved original C1 assertion identifies this actual community derivative as a continuous function on its unique-derivative domain. -/
theorem diagonalPhysicalSlope_continuousOn (a : ℝ) (ha : -1<a) :
    ContinuousOn (diagonalPhysicalSlope a ha) (Ioc (0:ℝ) (1/2)) :=
  ((contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ioc (0:ℝ) (1/2))).mp
    (kernelDiagonal_contDiffOn a ha)).2

/-- The physical fold sends every actual interior point into the positive half domain.
Use: targetPotential_continuousOn and the reflected ODE localize original half-domain results without losing the midpoint.
Article: jacobi, Proposition 2.2.
Proof: both reflected distances are positive and their minimum is at most their midpoint. -/
theorem physicalFold_mem {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    min t (1-t)∈Ioc (0:ℝ) (1/2) := by
  refine ⟨lt_min ht.1 (by linarith [ht.2]),?_⟩
  by_cases h : t≤1/2
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

/-- The original full target potential is genuinely continuous throughout the physical interior, including the midpoint.
Use: the reflected target ODE is classical at every point and H_alpha realizes a continuous interior coefficient.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the proved true diagonal derivative and original reference coefficient are continuous on the half domain. Compose their sum with the continuous physical fold, whose range stays in that domain. -/
theorem targetPotential_continuousOn (a : ℝ) (ha : -1<a) :
    ContinuousOn (targetPotential a ha) (Ioo (0:ℝ) 1) := by
  have hq := (potential_continuousOn a).mono
    (show Ioc (0:ℝ) (1/2)⊆Ioo (0:ℝ) 1 from fun x hx => ⟨hx.1,by linarith [hx.2]⟩)
  exact (hq.add (continuousOn_const.mul (diagonalPhysicalSlope_continuousOn a ha))).comp
    (continuous_id.min (continuous_const.sub continuous_id)).continuousOn
    (fun _ ht => physicalFold_mem ht)

/-- The constructed full potential has its exact physical reflection symmetry.
Use: the full target differential equation reflects the same original coefficient, and the improper integral reduces to the genuine half primitive.
Article: jacobi, Theorem 2.1.
Proof: reflection interchanges the two arguments of the physical minimum. -/
theorem targetPotential_reflection (a : ℝ) (ha : -1<a) (t : ℝ) :
    targetPotential a ha (1-t)=targetPotential a ha t := by
  simp only [targetPotential,show (1:ℝ)-(1-t)=t by ring,min_comm]

/-- On its original half interval the full potential is exactly the genuine half-domain coefficient.
Use: the reflected ODE and the improper-mean FTC retain the literal original q+2*w' values.
Article: jacobi, Theorem 2.1.
Proof: the physical fold fixes every point at or left of the midpoint. -/
theorem targetPotential_half (a : ℝ) (ha : -1<a) {t : ℝ} (ht : t≤1/2) :
    targetPotential a ha t=halfTargetPotential a ha t := by
  rw [targetPotential,min_eq_left (by linarith)]

/-- The canonical actual diagonal derivative agrees with each original positive-strip derivative away from that strip's lower endpoint.
Use: targetPotential_strip identifies the genuine global coefficient with the proved actual transformed ODE coefficient.
Article: jacobi, Theorem 2.1.
Proof: the closed strip is a relative neighborhood in the original half domain at this point. Transfer the independently proved true strip derivative to that domain and use uniqueness of its actual derivative. -/
theorem diagonalPhysicalSlope_strip {a d t : ℝ} (ha : -1<a) (hd : 0<d)
    (ht : t∈Ioc d (1/2)) :
    diagonalPhysicalSlope a ha t=diagonalSlopeRows ha hd (ht.1.le.trans ht.2) ⟨t,⟨ht.1.le,ht.2⟩⟩ := by
  -- The domains agree locally at the original point, including the midpoint's actual left neighborhood.
  have h := kernelDiagonal_hasDerivWithinAt ha hd
    ⟨t,⟨(hd.trans ht.1).le,ht.2⟩⟩ ht.1.le
  have hm : Icc d (1/2)∈𝓝[Ioc (0:ℝ) (1/2)] t := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht.1)] with x hx hdx
    exact ⟨hdx.le,hx.2⟩
  exact (h.mono_of_mem_nhdsWithin hm).derivWithin
    (uniqueDiffOn_Ioc (0:ℝ) (1/2) t ⟨hd.trans ht.1,ht.2⟩)

/-- The full target potential is the original proved ODE coefficient on every interior positive half strip.
Use: fullWave_ODE transports the actual original transformed equation through genuine midpoint reflection.
Article: jacobi, Theorem 2.1.
Proof: the fold fixes the original coordinate, and uniqueness identifies the genuine diagonal derivative with the actual strip derivative. -/
theorem targetPotential_strip {a d t : ℝ} (ha : -1<a) (hd : 0<d) (hds : d≤(1/2:ℝ))
    (ht : t∈Ioc d (1/2)) :
    targetPotential a ha t=transformedPotentialStrip a ha hd hds ⟨t,⟨ht.1.le,ht.2⟩⟩ := by
  rw [targetPotential_half a ha ht.2,halfTargetPotential,diagonalPhysicalSlope_strip ha hd ht]
  rfl

end
end jacobi.GelfandLevitan
