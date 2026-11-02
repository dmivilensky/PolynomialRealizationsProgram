import jacobi.Fredholm.Normalization

/-!
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
The genuine optimizer supplies a continuous strictly decreasing affine
Green coordinate. Its positive half-core maps bijectively onto (0,1),
including the full-support endpoint. No candidate inverse is assumed.
Source: the proved actual Green shape, its free limit and intermediate values.
Use: the positive part of this coordinate describes the density on the entire line.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Elliptic
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The affine Green coordinate of the actual Fredholm optimizer.
Use: the positive part of this coordinate describes the density on the entire line.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
-/
def Optimizer.coordinate {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) (x : ℝ) : ℝ :=
  (P.g hs.le x-P.edge)/(P.g hs.le 0-P.edge)

/-- The actual affine coordinate is continuous, even and equals one at the central turn.
Use: initializes the measurable half-core and reflection in the genuine integral substitution.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: the genuine Green diagonal is C2 and even; its central switching gap is strictly positive. -/
theorem Optimizer.coordinate_regular {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    Continuous (P.coordinate hs) ∧ (∀ x,P.coordinate hs (-x)=P.coordinate hs x) ∧
      P.coordinate hs 0=1 := by
  have hc := (P.density.greenDiagonal_contDiff P.continuous hs.le P.pole).continuous
  refine ⟨(hc.sub continuous_const).div_const _,?_,?_⟩
  · intro x
    simp only [Optimizer.coordinate,(P.shape hs).2.2.1 x]
  · exact div_self (sub_pos.mpr (P.shape hs).1).ne'

/-- The genuine normalized Green branch is strictly decreasing on the positive half-line.
Use: supplies actual injectivity and excludes extraneous branches in the quadrature change of variables.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: the actual C2 Green diagonal has strictly negative derivative at
every positive radius; division by its positive central switching gap preserves strict order. -/
theorem Optimizer.coordinate_strictAnti {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    StrictAntiOn (P.coordinate hs) (Ici (0:ℝ)) := by
  have hc := P.density.greenDiagonal_contDiff P.continuous hs.le P.pole
  have hg : StrictAntiOn (P.g hs.le) (Ici (0:ℝ)) :=
    strictAntiOn_of_deriv_neg (convex_Ici 0) hc.continuous.continuousOn
      (fun x hx => (P.shape hs).2.2.2 x (by simpa only [interior_Ici,mem_Ioi] using hx))
  intro x hx y hy hxy
  exact (div_lt_div_iff_of_pos_right (sub_pos.mpr (P.shape hs).1)).mpr
    (sub_lt_sub_right (hg hx hy hxy) P.edge)

/-- The actual normalized coordinate has the exact free-state tail limit.
Use: every level in (0,1) is attained in the genuine positive-density half-core.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: affine normalization preserves the previously proved actual free Green limit. -/
theorem Optimizer.coordinate_limit {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    Tendsto (P.coordinate hs) atTop (𝓝 (((1/2:ℝ)-P.edge)/(P.g hs.le 0-P.edge))) :=
  (((green_diagonal_limits P.density hs.le P.pole).1.sub_const P.edge).div_const _)

/-- The positive-density half-core of the actual Fredholm optimizer.
Use: a common measurable substitution domain handles compact and full support.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
-/
def Optimizer.core {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) : Set ℝ :=
  Ioi (0:ℝ) ∩ (P.coordinate hs) ⁻¹' Ioi 0

/-- The genuine half-core is measurable.
Use: discharges the domain hypothesis in the Lebesgue Jacobian theorem.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: both positivity conditions define open sets by actual coordinate continuity. -/
theorem Optimizer.core_measurable {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    MeasurableSet (P.core hs) :=
  measurableSet_Ioi.inter ((P.coordinate_regular hs).1.measurable measurableSet_Ioi)

/-- The genuine positive half-core maps bijectively onto the full printed open quadrature interval.
Use: proves actual surjectivity rather than assuming an inverse profile exists.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: strict radial decrease gives the forward inclusion. For each level
between zero and one, the true nonpositive limiting coordinate supplies a
finite point below that level; intermediate values between that point and
the central value one give an actual positive-radius preimage. -/
theorem Optimizer.coordinate_image {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    P.coordinate hs '' P.core hs=Ioo (0:ℝ) 1 := by
  -- The inverse point is constructed separately for each interior level.
  have hc := (P.coordinate_regular hs).1
  have hcenter := (P.coordinate_regular hs).2.2
  apply subset_antisymm
  · rintro v ⟨x,hx,rfl⟩
    have hh := P.coordinate_strictAnti hs (show (0:ℝ)∈Ici 0 by simp)
      (mem_Ici.mpr (mem_Ioi.mp hx.1).le) hx.1
    rw [hcenter] at hh
    exact ⟨hx.2,hh⟩
  · intro v hv
    have htail : ((1/2:ℝ)-P.edge)/(P.g hs.le 0-P.edge)<v :=
      (div_nonpos_of_nonpos_of_nonneg (by linarith [(P.parameter_signs hs).1])
        (sub_pos.mpr (P.shape hs).1).le).trans_lt hv.1
    obtain ⟨R,hR,hbelow⟩ := ((eventually_gt_atTop (0:ℝ)).and
      ((P.coordinate_limit hs).eventually (Iio_mem_nhds htail))).exists
    obtain ⟨x,hx,hvalue⟩ := intermediate_value_Icc' hR.le hc.continuousOn
      (show v∈Icc (P.coordinate hs R) (P.coordinate hs 0) by rw [hcenter]; exact ⟨hbelow.le,hv.2.le⟩)
    have hpos : 0<x := lt_of_le_of_ne hx.1 (by
      intro heq
      rw [← heq,hcenter] at hvalue
      exact hv.2.ne' hvalue)
    exact ⟨x,⟨hpos,by change 0<P.coordinate hs x; rw [hvalue]; exact hv.1⟩,hvalue⟩

/-- The actual Green diagonal is recovered exactly from its normalized coordinate.
Use: the common polynomial identity applies pointwise to the genuine optimizer.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: cancel the strictly positive actual central switching gap in the defining affine coordinate. -/
theorem Optimizer.coordinate_affine {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) (x : ℝ) :
    P.g hs.le x=P.edge+(P.g hs.le 0-P.edge)*P.coordinate hs x := by
  unfold Optimizer.coordinate
  field_simp [(sub_pos.mpr (P.shape hs).1).ne']
  ring

/-- The actual normalized coordinate has its genuine classical derivative everywhere.
Use: the true first integral determines the absolute Jacobian on the positive half-core.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
Proof: differentiate the actual C2 Green diagonal and divide by its constant central switching gap. -/
theorem Optimizer.coordinate_hasDerivAt {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) (x : ℝ) :
    HasDerivAt (P.coordinate hs) (deriv (P.g hs.le) x/(P.g hs.le 0-P.edge)) x :=
  (((P.density.greenDiagonal_contDiff P.continuous hs.le P.pole).differentiable (by norm_num) x).hasDerivAt.sub_const P.edge).div_const _

end
end jacobi.Fredholm
