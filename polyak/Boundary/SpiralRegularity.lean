import polyak.Boundary.SpiralDerivative

/-! Article: actual boundary regularity on the complete exact spiral regime. -/
namespace polyak.Boundary
noncomputable section
open Spectral
open scoped Topology

/-- Article: the closed exponent set of the optimal spiral arc. -/
def spiralExponentArc : Set ℝ := {t | G1 ≤ Real.cosh t ∧ Real.cosh t ≤ GW}

/-- Article: exact derivative of V within the entire closed spiral regime. -/
theorem hasDerivWithinAt_V_spiral {t : ℝ} (ht : t∈spiralExponentArc) :
    HasDerivWithinAt V (spiralBoundaryDerivative t) spiralExponentArc t := by
  apply (hasDerivAt_spiralBoundary t).hasDerivWithinAt.congr_of_mem ?_ ht
  intro s hs
  exact spiral_optimal hs.1 hs.2

/-- Article: ordinary derivative of V in the open optimal spiral regime. -/
theorem hasDerivAt_V_spiral {t : ℝ} (hl : G1<Real.cosh t) (hu : Real.cosh t<GW) :
    HasDerivAt V (spiralBoundaryDerivative t) t := by
  apply (hasDerivWithinAt_V_spiral ⟨hl.le,hu.le⟩).hasDerivAt
  have hn : {s : ℝ | G1<Real.cosh s ∧ Real.cosh s<GW}∈𝓝 t :=
    ((isOpen_lt continuous_const Real.continuous_cosh).inter
      (isOpen_lt Real.continuous_cosh continuous_const)).mem_nhds ⟨hl,hu⟩
  exact Filter.mem_of_superset hn (fun _ hs => ⟨hs.1.le,hs.2.le⟩)

/-- Article: the actual spiral boundary has absolute derivative strictly below one. -/
theorem abs_deriv_V_spiral_lt_one {t : ℝ} (hl : G1<Real.cosh t) (hu : Real.cosh t<GW) :
    |deriv V t|<1 := by
  rw [(hasDerivAt_V_spiral hl hu).deriv]
  exact abs_spiralBoundaryDerivative_lt_one t

/-- Article: the exact spiral interval is nondegenerate. -/
theorem G1_lt_GW : G1<GW := by
  have hs:=Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn:=Real.sqrt_nonneg (3 : ℝ)
  have h:=G1_bounds.2
  unfold GW
  nlinarith

end
end polyak.Boundary
