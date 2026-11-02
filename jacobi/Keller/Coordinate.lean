import jacobi.Keller.FirstIntegral
import jacobi.Keller.Weights
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
Article: jacobi, Theorem D.6.
The actual normalized positive ground state decreases from one toward zero.
The coordinate sigma=sqrt(c*(1-u²)) is strictly increasing on the positive
half-line. Its positive-density domain maps bijectively onto (0,1).
The true first integral supplies the exact printed square-root Jacobian.
Source: intermediate values, the actual ground-state derivative and the proved zero first integral.
Use: the Keller coordinate has a nonnegative square-root argument on the entire line.
-/
namespace jacobi.Keller
noncomputable section
open MeasureTheory Real Set Filter jacobi.Variational
open chebyshev2.Sobolev
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {m : Density} {ell M : ℝ}

/-- The actual normalized ground state never exceeds its central value one.
Use: the Keller coordinate has a nonnegative square-root argument on the entire line.
Article: jacobi, Theorem D.6.
Proof: strict radial decrease bounds nonnegative arguments by the center; reflect negative arguments. -/
theorem Profile.upper_bound (p : Profile m ell M) (x : ℝ) : H1.rep p.u x≤1 := by
  have hh (y : ℝ) (hy : 0≤y) : H1.rep p.u y≤1 := by
    have h := p.decreasing.antitoneOn (show (0:ℝ)∈Ici 0 by simp) hy hy
    rwa [p.center] at h
  rcases le_total 0 x with hx | hx
  · exact hh x hx
  · rw [← p.even x]
    exact hh (-x) (neg_nonneg.mpr hx)

/-- The actual normalized ground state maps the positive half-line onto the whole open unit interval.
Use: establishes surjectivity of the optimizing quadrature coordinate without assuming a profile inverse.
Article: jacobi, Theorem D.6.
Proof: strict decrease and positivity give one inclusion. Decay at infinity
and the actual intermediate value theorem give every interior level. -/
theorem Profile.state_image (p : Profile m ell M) : H1.rep p.u '' Ioi (0:ℝ)=Ioo (0:ℝ) 1 := by
  -- A finite right endpoint is selected separately for each requested interior level.
  apply subset_antisymm
  · rintro y ⟨x,hx,rfl⟩
    have hh := p.decreasing (show (0:ℝ)∈Ici 0 by simp) (mem_Ici.mpr (mem_Ioi.mp hx).le) hx
    rw [p.center] at hh
    exact ⟨p.positive x,hh⟩
  · intro y hy
    obtain ⟨r,hr,hry⟩ := ((eventually_gt_atTop (0:ℝ)).and
      ((H1.rep_tendsto_zero p.u).1.eventually (Iio_mem_nhds hy.1))).exists
    obtain ⟨x,hx,hxy⟩ := intermediate_value_Icc' hr.le (H1.continuous_rep p.u).continuousOn
      (show y∈Icc (H1.rep p.u r) (H1.rep p.u 0) by rw [p.center]; exact ⟨hry.le,hy.2.le⟩)
    refine ⟨x,?_,hxy⟩
    apply lt_of_le_of_ne hx.1
    intro hz
    rw [← hz,p.center] at hxy
    exact hy.2.ne' hxy

/-- The actual Keller change of variables sigma=sqrt(c*(1-u²)).
Use: maps the optimizing positive half-core to the source's fixed quadrature interval.
Article: jacobi, Theorem D.6.
-/
def Profile.coordinate (p : Profile m ell M) (x : ℝ) : ℝ := sqrt (p.shape*(1-H1.rep p.u x^2))

/-- The Keller coordinate is a genuine continuous function on the whole line.
Use: its open positive-core domain is measurable in the Lebesgue Jacobian theorem.
Article: jacobi, Theorem D.6.
Proof: the actual H1 representative is continuous and square root is continuous everywhere. -/
theorem Profile.coordinate_continuous (p : Profile m ell M) : Continuous p.coordinate := by
  have hu := H1.continuous_rep p.u
  unfold Profile.coordinate
  fun_prop

/-- The actual Keller coordinate has its exact defining square everywhere.
Use: derives the density and Jacobian algebra on the same original optimizer.
Article: jacobi, Theorem D.6.
Proof: the proved normalized peak bound makes the square-root argument nonnegative. -/
theorem Profile.coordinate_sq (p : Profile m ell M) (hell : 0<ell) (x : ℝ) :
    p.coordinate x^2=p.shape*(1-H1.rep p.u x^2) := by
  apply sq_sqrt
  have hc := p.shape_ge_one hell
  have hu := p.upper_bound x
  have hp := p.positive x
  exact mul_nonneg (by linarith) (by nlinarith)

/-- The actual Keller coordinate is strictly positive away from its central turning point.
Use: licenses the classical square-root derivative and all Jacobian denominator cancellations.
Article: jacobi, Theorem D.6.
Proof: strict radial decrease gives 0<u(x)<1 while c>=1. -/
theorem Profile.coordinate_pos (p : Profile m ell M) (hell : 0<ell) {x : ℝ} (hx : 0<x) :
    0<p.coordinate x := by
  have hu := p.decreasing (show (0:ℝ)∈Ici 0 by simp) hx.le hx
  rw [p.center] at hu
  apply sqrt_pos.mpr
  exact mul_pos (zero_lt_one.trans_le (p.shape_ge_one hell)) (by nlinarith [p.positive x])

/-- The coordinate is injective on the actual positive half-line.
Use: the quadrature map satisfies the genuine injectivity premise of the Jacobian theorem.
Article: jacobi, Theorem D.6.
Proof: positive ground values strictly decrease, so c*(1-u²) and its square root strictly increase. -/
theorem Profile.coordinate_strictMono (p : Profile m ell M) (hell : 0<ell) :
    StrictMonoOn p.coordinate (Ioi (0:ℝ)) := by
  intro x hx y hy hxy
  have hux := p.positive x
  have huy := p.positive y
  have hanti := p.decreasing (mem_Ici.mpr (mem_Ioi.mp hx).le) (mem_Ici.mpr (mem_Ioi.mp hy).le) hxy
  apply (sq_lt_sq₀ (p.coordinate_pos hell hx).le (p.coordinate_pos hell hy).le).mp
  rw [p.coordinate_sq hell,p.coordinate_sq hell]
  exact mul_lt_mul_of_pos_left (by nlinarith) (zero_lt_one.trans_le (p.shape_ge_one hell))

/-- The original ground cutoff and the optimizing coordinate have the exact positive-part relation.
Use: both support localization and density normalization refer to the actual optimizer, including c=1.
Article: jacobi, Theorem D.6.
Proof: combine the coordinate square with c*(1-v_e)=1 from the proved finite cutoff gap. -/
theorem Profile.coordinate_gap (p : Profile m ell M) (hell : 0<ell) (x : ℝ) :
    p.shape*(H1.rep p.u x^2-p.edge)=1-p.coordinate x^2 := by
  have hh : p.shape*(1-p.edge)=1 := inv_mul_cancel₀ (sub_pos.mpr (p.edge_lt_one hell)).ne'
  have hs := p.coordinate_sq hell x
  nlinarith

/-- The actual positive-density half-core, expressed in the optimizing coordinate.
Use: the same measurable domain handles both finite support and the free-mass whole-line profile.
Article: jacobi, Theorem D.6.
-/
def Profile.core (p : Profile m ell M) : Set ℝ := Ioi (0:ℝ)∩p.coordinate ⁻¹' Iio 1

/-- The actual half-core is measurable.
Use: supplies the domain premise in the genuine Lebesgue change of variables.
Article: jacobi, Theorem D.6.
Proof: it is the intersection of two open sets because the coordinate is continuous. -/
theorem Profile.core_measurable (p : Profile m ell M) : MeasurableSet p.core :=
  measurableSet_Ioi.inter (p.coordinate_continuous.measurable measurableSet_Iio)

/-- The actual Keller half-core maps onto exactly the printed open quadrature interval.
Use: discharges surjectivity of the coordinate used to compute the optimizer's mass and energy.
Article: jacobi, Theorem D.6.
Proof: for each sigma in (0,1), the ground level sqrt(1-sigma²/c) lies
strictly between zero and one. The proved full ground branch attains that
level; the exact coordinate square and positivity identify its coordinate. -/
theorem Profile.coordinate_image (p : Profile m ell M) (hell : 0<ell) :
    p.coordinate '' p.core=Ioo (0:ℝ) 1 := by
  -- A genuine attained ground level constructs the inverse point rather than assuming a quadrature parametrization.
  apply subset_antisymm
  · rintro v ⟨x,hx,rfl⟩
    exact ⟨p.coordinate_pos hell hx.1,hx.2⟩
  · intro v hv
    have hc : 0<p.shape := zero_lt_one.trans_le (p.shape_ge_one hell)
    have hv2 : v^2<1 := by nlinarith [hv.1,hv.2,sq_nonneg (1-v)]
    have hP : 0<1-v^2/p.shape := by rw [sub_pos,div_lt_one hc]; exact hv2.trans_le (p.shape_ge_one hell)
    have hlev : sqrt (1-v^2/p.shape)∈Ioo (0:ℝ) 1 := by
      refine ⟨sqrt_pos.mpr hP,?_⟩
      exact (sqrt_lt' zero_lt_one).mpr (by have hdiv := div_pos (sq_pos_of_pos hv.1) hc; nlinarith)
    obtain ⟨x,hx,hux⟩ := (show sqrt (1-v^2/p.shape)∈H1.rep p.u '' Ioi (0:ℝ) from by
      rw [p.state_image]; exact hlev)
    have hcoord : p.coordinate x=v := by
      apply (sq_eq_sq₀ (p.coordinate_pos hell hx).le hv.1.le).mp
      rw [p.coordinate_sq hell,hux,sq_sqrt hP.le]
      field_simp
      ring
    exact ⟨x,⟨hx,by change p.coordinate x<1; rw [hcoord]; exact hv.2⟩,hcoord⟩

end
end jacobi.Keller
