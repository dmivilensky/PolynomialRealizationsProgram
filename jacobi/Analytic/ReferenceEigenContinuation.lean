import jacobi.Analytic.ReferenceEnergySeries
import jacobi.Analytic.ContinuousMapHolomorphy
import jacobi.Reference.Solutions
import jacobi.Reference.WeightedSpace

/-!
Article: jacobi, Lemma C.1.
On the actual reference spectrum, the continued Gauss series terminates
exactly. Its genuine full-interval eigenfunction is therefore a finite
polynomial times the original complex sine power. It is holomorphic in
the continuous-function norm, including both zero spatial endpoints.
Use: one connected domain supports the complex integral norm identity by analytic continuation.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Metric Filter
open jacobi.Reference (Interval)
open scoped Topology
attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual admissible complex reference-order half-plane.
Use: one connected domain supports the complex integral norm identity by analytic continuation.
Article: jacobi, Lemma C.1.
-/
def referenceOrders : Set ℂ := {a | 0<(gamma a).re}

/-- The genuine reference-order half-plane is open.
Use: the Banach-valued Cauchy theorem applies to the original full-interval eigenfunctions.
Article: jacobi, Lemma C.1.
Proof: the real part of the actual affine exponent is continuous. -/
theorem referenceOrders_open : IsOpen referenceOrders :=
  isOpen_lt continuous_const (by unfold gamma; fun_prop)

/-- The actual complex sine prefactor is jointly continuous on the full closed physical interval at every admissible order.
Use: its continuous-function-valued family is norm continuous, including at both singular endpoints.
Article: jacobi, Lemma C.1.
Proof: sine is nonnegative on the physical unit interval. Apply community joint continuity of the genuine complex power at an exponent with positive real part. -/
theorem weight_joint_unit {a:ℂ} (ha:a∈referenceOrders) (t:Interval) :
    ContinuousAt (fun p:ℂ × Interval => weight p.1 p.2) (a,t) := by
  have hs : 0≤Real.sin (Real.pi*(t:ℝ))/Real.pi := div_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le t.property.1)
      (by nlinarith [Real.pi_pos,t.property.2])) Real.pi_pos.le
  exact (Complex.continuousAt_cpow_of_re_pos
    (p := (((Real.sin (Real.pi*(t:ℝ))/Real.pi:ℝ):ℂ),gamma a))
    (Or.inl (by simpa only [Complex.ofReal_re] using hs)) ha).comp_of_eq
    (f := fun p:ℂ × Interval => (((Real.sin (Real.pi*(p.2:ℝ))/Real.pi:ℝ):ℂ),gamma p.1))
    (by unfold gamma; fun_prop) rfl

/-- The genuine complex reference sine prefactor as a full-interval continuous function.
Use: multiplies the finite spectral polynomial before its actual squared integral is taken.
Article: jacobi, Lemma C.1.
-/
def weightUnitMap (a:ℂ) : C(Interval,ℂ) := by
  classical
  exact if ha:a∈referenceOrders then
    ⟨fun t => weight a t,continuous_iff_continuousAt.mpr (fun t =>
      (weight_joint_unit ha t).comp_of_eq (f := fun s:Interval => (a,s)) (by fun_prop) rfl)⟩ else 0

/-- The continuous-function prefactor evaluates to its original literal complex power.
Use: identifies all norm-valued constructions with the source pointwise formula.
Article: jacobi, Lemma C.1.
Proof: select the proved admissible branch. -/
theorem weightUnitMap_apply {a:ℂ} (ha:a∈referenceOrders) (t:Interval) :
    weightUnitMap a t=weight a t := by simp only [weightUnitMap,dite_eq_left ha,ContinuousMap.coe_mk]

/-- The genuine full-interval sine prefactor is holomorphic in its actual continuous-function norm.
Use: the finite reference eigenfunction and its original squared integral are Banach holomorphic.
Article: jacobi, Lemma C.1.
Proof: joint continuity on the order half-plane times the compact interval gives norm continuity. Each point evaluation is the already proved actual analytic complex power. Apply the continuous-function-valued Cauchy theorem. -/
theorem weightUnitMap_holomorphic : DifferentiableOn ℂ weightUnitMap referenceOrders := by
  -- The same actual complex power is used at the physical endpoints and interior.
  have hc : ContinuousOn weightUnitMap referenceOrders := by
    apply ContinuousMap.continuousOn_of_continuousOn_uncurry
    intro p hp
    apply (weight_joint_unit hp.1 p.2).continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ hp
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact weightUnitMap_apply hq.1 q.2
  apply jacobi.Analytic.continuousMap_differentiableOn referenceOrders_open hc
  intro t a ha
  apply (weight_comp_analytic analyticAt_id ha (t:ℝ)).differentiableAt.differentiableWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with b hb
    exact weightUnitMap_apply hb t
  · exact weightUnitMap_apply ha t

/-- The fixed full-interval powers of the genuine Jacobi cosine coordinate.
Use: the reference spectral polynomial is a finite sum of these same spatial functions with analytic order coefficients.
Article: jacobi, Lemma C.1.
-/
def referenceCoordinatePower (n:ℕ) : C(Interval,ℂ) :=
  ⟨fun t => (((1-Real.cos (Real.pi*(t:ℝ)))/2:ℝ):ℂ)^n,by fun_prop⟩

/-- The literal finite reference polynomial, with its original complex Gauss coefficients.
Use: packages the genuine full-interval reference eigenfunction without relying on convergence at the right Gauss endpoint.
Article: jacobi, Lemma C.1.
-/
def referencePolynomialMap (a:ℂ) (k:ℕ) : C(Interval,ℂ) :=
  ∑ n∈Finset.range (k+1),
    jacobi.Jacobi.coefficient (gamma a-1/2) (gamma a-1/2) k n • referenceCoordinatePower n

/-- The actual finite reference polynomial is holomorphic in the continuous-function norm on the entire admissible order half-plane.
Use: makes the original eigenfunction's bilinear norm integral genuinely holomorphic.
Article: jacobi, Lemma C.1.
Proof: every genuine coefficient has positive-real-part denominator and is analytic in order. Its product with a fixed continuous spatial vector is Banach holomorphic; add the finitely many terms. -/
theorem referencePolynomialMap_holomorphic (k:ℕ) :
    DifferentiableOn ℂ (fun a => referencePolynomialMap a k) referenceOrders := by
  -- Every finite coefficient multiplies a fixed continuous spatial vector, so no endpoint series limit is needed.
  intro a ha
  unfold referencePolynomialMap
  apply DifferentiableWithinAt.fun_sum
  intro n _
  have hcoef := jacobi.Reference.Hypergeometric.coefficient_comp_analytic (p := a)
    (A := fun _ : ℂ => -(k:ℂ)) (B := fun a:ℂ => (k:ℂ)+(gamma a-1/2)+(gamma a-1/2)+1)
    (C := fun a:ℂ => gamma a-1/2+1) analyticAt_const (by unfold gamma; fun_prop)
    (by unfold gamma; fun_prop) (by norm_num; linarith [show 0<(gamma a).re from ha]) n
  exact hcoef.differentiableAt.differentiableWithinAt.smul_const (referenceCoordinatePower n)

/-- The genuine entire physical reference eigenfunction continued in order.
Use: its true squared spatial integral is identified with the printed Gamma norm formula.
Article: jacobi, Lemma C.1.
-/
def referenceEigenMap (a:ℂ) (k:ℕ) : C(Interval,ℂ) := weightUnitMap a*referencePolynomialMap a k

/-- The continued actual reference eigenfunction is holomorphic in the full-interval supremum norm.
Use: the genuine squared reference norm integral is holomorphic, including both physical endpoints.
Article: jacobi, Lemma C.1.
Proof: multiply the proved holomorphic sine-prefactor and finite-polynomial maps in their actual continuous-function Banach algebra. -/
theorem referenceEigenMap_holomorphic (k:ℕ) :
    DifferentiableOn ℂ (fun a => referenceEigenMap a k) referenceOrders :=
  weightUnitMap_holomorphic.mul (referencePolynomialMap_holomorphic k)

/-- At its actual reference spectrum the original energy solution equals the genuine finite-polynomial reference vector exactly.
Use: the complex integral norm formula concerns the same original f, not a separately continued eigenfunction.
Article: jacobi, Lemma C.1.
Proof: choose the actual affine frequency grid, whose square is the original reference energy shift. The two Gauss numerator parameters become -k and k+2*gamma. Its terminating Jacobi sum is exactly the finite spatial vector above. -/
theorem solution_at_reference_complex {a:ℂ} (ha:a∈referenceOrders) (k:ℕ) (t:Interval) :
    solution a (jacobi.Hankel.frequencyReference a k) t=referenceEigenMap a k t := by
  -- Termination is an exact finite identity, so the endpoint Gauss argument one causes no convergence assumption.
  rw [solution_eq_wave a (omega := jacobi.Hankel.frequencyGrid a k) (by
    unfold jacobi.Hankel.frequencyReference; ring) t]
  have h1 : gamma a- jacobi.Hankel.frequencyGrid a k/(Real.pi:ℂ)=-(k:ℂ) := by
    unfold gamma jacobi.Hankel.frequencyGrid
    field_simp
    ring
  have h2 : gamma a+ jacobi.Hankel.frequencyGrid a k/(Real.pi:ℂ)=
      (k:ℂ)+(gamma a-1/2)+(gamma a-1/2)+1 := by
    unfold gamma jacobi.Hankel.frequencyGrid
    field_simp
    ring
  change weight a t*ordinaryHypergeometric _ _ _ _=referenceEigenMap a k t
  rw [h1,h2]
  have he : (gamma a+1/2)=(gamma a-1/2)+1 := by ring
  rw [he]
  have hx : (jacobi.Reference.coordinate (t:ℝ):ℂ)=(1-(Real.cos (Real.pi*(t:ℝ)):ℂ))/2 := by
    unfold jacobi.Reference.coordinate
    push_cast
    rfl
  rw [hx]
  change weight a t* jacobi.Jacobi.normalized (gamma a-1/2) (gamma a-1/2) k
    ((Real.cos (Real.pi*(t:ℝ)):ℝ):ℂ)=_
  rw [jacobi.Jacobi.normalized_eq_sum]
  simp only [referenceEigenMap,ContinuousMap.mul_apply,weightUnitMap_apply ha,referencePolynomialMap,
    ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,referenceCoordinatePower,ContinuousMap.coe_mk]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  congr 2
  push_cast
  rfl

end
end jacobi.ComplexReference
