import polyak.Boundary.P5.ContinuationBounds
import polyak.Boundary.P5.WeightSigns
import polyak.Boundary.P5.SpiralStrict

/-! Article: Proposition p5arc on its complete closed physical domain.
Every source equation, box reserve, signed lag and infinite tail is discharged. -/
noncomputable section
namespace polyak.Boundary.P5
open Spectral

theorem physicalDomain_subset {h : ℝ} (hh : h∈Set.Icc (0 : ℝ) (P2.Ga-1)) :
    h∈Set.Icc (0 : ℝ) (11791/500000) := ⟨hh.1,hh.2.trans centralEndpoint_lt.le⟩

/-- The exact actual boundary formula on the whole closed P5 arc, including the three-cycle. -/
theorem continuation_optimal {h t : ℝ} (hh : h∈Set.Icc (0 : ℝ) (P2.Ga-1))
    (ht : Real.cosh t=1+h) : V t=Real.arsinh (branchU h (Selection.continuation h)) := by
  have hD := physicalDomain_subset hh
  by_cases hz : h=0
  · have ht0 : t=0 := by
      by_contra hn
      have hc := Real.one_lt_cosh.mpr hn
      rw [ht,hz] at hc
      norm_num at hc
    subst h
    subst t
    simpa only [branchU,zero_mul,add_zero] using critical_boundary_value
  · exact sourceRoot_optimal (continuation_geometry ⟨lt_of_le_of_ne hh.1 (Ne.symm hz),hD.2⟩)
      (Selection.continuation_source hD) (continuation_weight5_nonneg hh.1 hh.2) ht
      (continuation_prefix hD)

/-- The genuine infinite feasible two-atom spectrum on every positive point of P5. -/
theorem continuation_feasible {h t : ℝ} (hh : h∈Set.Ioc (0 : ℝ) (P2.Ga-1))
    (ht : Real.cosh t=1+h) :
    ∃ (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (x y : Frequency) (C : ℝ),
      Feasible (V t) t (twoAtomSpectrum p hp0 hp1 x y) C := by
  have hD := physicalDomain_subset ⟨hh.1.le,hh.2⟩
  let hb := continuation_geometry ⟨hh.1,hD.2⟩
  refine ⟨h*Selection.continuation h 3,mul_nonneg hh.1.le hb.tail.P_band.1.le,
    hb.mass_lt_one.le,⟨branchX h (Selection.continuation h),
      ⟨hb.tail.x_interior.1.le,hb.tail.x_interior.2.le⟩⟩,
    ⟨Selection.continuation h 2,⟨hb.tail.y_interior.1.le,hb.tail.y_interior.2.le⟩⟩,
    h*Selection.continuation h 4/Real.sinh t,?_⟩
  rw [continuation_optimal ⟨hh.1.le,hh.2⟩ ht]
  unfold Feasible
  rw [Real.sinh_arsinh]
  exact sourceRoot_feasible hb ht (continuation_prefix hD)

/-- Strict improvement over the spiral throughout the noncritical central arc. -/
theorem continuation_strict_spiral {h t : ℝ} (hh : h∈Set.Ioc (0 : ℝ) (P2.Ga-1))
    (ht : Real.cosh t=1+h) : Real.arsinh (1-1/(2*Real.cosh t))<V t := by
  obtain ⟨slab,hm,hs,hX⟩ := continuation_checkedBox (physicalDomain_subset ⟨hh.1.le,hh.2⟩)
  rw [continuation_optimal ⟨hh.1.le,hh.2⟩ ht,ht]
  exact Real.arsinh_strictMono (spiral_improvement_of_box hm hh.1 hs hX)

end polyak.Boundary.P5
