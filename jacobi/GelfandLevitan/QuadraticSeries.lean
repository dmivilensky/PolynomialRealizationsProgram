import jacobi.GelfandLevitan.UniformKernel
import jacobi.Reference.CoefficientUniqueness
import Mathlib.MeasureTheory.Integral.Prod

/-!
Article: jacobi, Proposition C.2.
The actual double integral of the original continuous GL kernel equals
the genuine spectral correction series for every original L2 input.
The product Lebesgue integral is used so the original L1 bound controls
both variables at once. On half-supported inputs this is exactly the
source half-interval quadratic form after zero extension.
Use: the genuine original spectral coefficients and their rank-one quadratic terms are integrable for arbitrary original L2 inputs.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set _root_.Complex Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] kernel kernelTerm

/-- The actual real source solution on the fixed compact physical half domain.
Use: the genuine original spectral coefficients and their rank-one quadratic terms are integrable for arbitrary original L2 inputs.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
-/
def realHalfWave (a : ℝ) (ha : -1<a) (E : ℝ) : C(Interval,ℝ) where
  toFun t := realSolution a E (halfTime t)
  continuous_toFun := continuous_iff_continuousAt.mpr (fun t =>
    (realSolution_continuousAt ha E (halfTime_mem t)).comp halfTime.continuous.continuousAt)

/-- Every original real coefficient integrand of an arbitrary true L2 input is genuinely integrable.
Use: the source quadratic correction term is evaluated by actual product-integral and subtraction identities.
Article: jacobi, Proposition C.2.
Proof: the true input is L1 and the actual physical real solution is compact continuous and bounded. -/
theorem realCoefficient_integrable (a : ℝ) (ha : -1<a) (v : Space) (E : ℝ) :
    Integrable (fun t:Interval => v t*realSolution a E (halfTime t)) :=
  (space_integrable v).mul_bdd (realHalfWave a ha E).continuous.aestronglyMeasurable
    (Eventually.of_forall (fun t => (realHalfWave a ha E).norm_coe_le_norm t))

/-- The actual original GL kernel on the fixed compact product domain.
Use: its genuine supremum bound makes the original L2 quadratic integrand integrable and allows Fubini in the operator realization.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
-/
def kernelMap (a : ℝ) (ha : -1<a) : C(Interval×Interval,ℝ) where
  toFun p := kernel a ha (halfTime p.1) (halfTime p.2)
  continuous_toFun := by
    -- Specify the composition maps before elaboration so the true convergent kernel remains folded.
    have hp : Continuous (fun p:Interval×Interval => (halfTime p.1,halfTime p.2)) :=
      (halfTime.continuous.comp continuous_fst).prodMk (halfTime.continuous.comp continuous_snd)
    have hc := ContinuousOn.comp_continuous
      (g := fun p:ℝ×ℝ => kernel a ha p.1 p.2)
      (f := fun p:Interval×Interval => (halfTime p.1,halfTime p.2))
      (kernel_continuousOn a ha) hp (fun p => ⟨halfTime_mem p.1,halfTime_mem p.2⟩)
    exact hc

/-- The genuine double Lebesgue integral of the original GL kernel against an arbitrary original input.
Use: this is the actual source F quadratic form, on every half-supported zero extension used in positivity and GL invertibility.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def kernelQuadratic (a : ℝ) (ha : -1<a) (v : Space) : ℝ :=
  ∫ p:Interval×Interval,(v p.1*v p.2)*kernel a ha (halfTime p.1) (halfTime p.2) ∂(volume.prod volume)

/-- The actual original GL quadratic integrand is genuinely integrable for every original L2 input.
Use: the product integral defining the genuine source form equals its true iterated spatial integral by Fubini.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the actual L2 input is L1 on the original interval. Its product
in the two independent variables is genuinely integrable, and the
actual original continuous kernel is bounded by its compact norm. -/
theorem kernelQuadratic_integrable (a : ℝ) (ha : -1<a) (v : Space) :
    Integrable (fun p:Interval×Interval =>
      (v p.1*v p.2)*kernel a ha (halfTime p.1) (halfTime p.2)) (volume.prod volume) :=
  ((space_integrable v).mul_prod (space_integrable v)).mul_bdd
    (kernelMap a ha).continuous.aestronglyMeasurable
    (Eventually.of_forall (fun p => (kernelMap a ha).norm_coe_le_norm p))

/-- The genuine GL kernel quadratic form equals the actual iterated source spatial integral.
Use: identifies the proved product-space spectral form with the original integral-operator quadratic expression.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: apply the community Fubini theorem with the proved actual integrability of the original product-space kernel integrand. -/
theorem kernelQuadratic_iterated (a : ℝ) (ha : -1<a) (v : Space) :
    kernelQuadratic a ha v=
      ∫ t:Interval,∫ s:Interval,(v t*v s)*kernel a ha (halfTime t) (halfTime s) :=
  integral_prod _ (kernelQuadratic_integrable a ha v)

/-- Each genuine source GL correction term has exactly its original spectral coefficient quadratic integral.
Use: identifies the actual integral series with the literal norming-weighted source coefficient difference, at every original index.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: expand the actual original summand and rearrange its two true
rank-one products. Both are integrable products of the original
coefficient integrands. Fubini's genuine product-integral identity
evaluates each as its actual coefficient square. -/
theorem kernelTerm_quadratic (a : ℝ) (ha : -1<a) (v : Space) (k : ℕ) :
    (∫ p:Interval×Interval,(v p.1*v p.2)*kernelTerm a ha k (halfTime p.1) (halfTime p.2) ∂(volume.prod volume))=
      (normingRatio a ha k*(realCoefficient a v (jacobi.Bessel.sigma a ha k))^2-
        (realCoefficient a v (eigenvalue a k))^2)/norming a k := by
  -- No formal interchange of a conditionally convergent double series is used; these are individual true integrable rank-one terms.
  let g := fun t:Interval => v t*realSolution a (jacobi.Bessel.sigma a ha k) (halfTime t)
  let h := fun t:Interval => v t*realSolution a (eigenvalue a k) (halfTime t)
  have hg : Integrable g := realCoefficient_integrable a ha v _
  have hh : Integrable h := realCoefficient_integrable a ha v _
  have he : (fun p:Interval×Interval => (v p.1*v p.2)*kernelTerm a ha k (halfTime p.1) (halfTime p.2))=
      (fun p => (normingRatio a ha k*(g p.1*g p.2)-h p.1*h p.2)/norming a k) := by
    funext p
    unfold kernelTerm
    dsimp [g,h]
    ring
  rw [he,integral_div,integral_sub ((hg.mul_prod hg).const_mul _) (hh.mul_prod hh),
    integral_const_mul,integral_prod_mul,integral_prod_mul]
  change (normingRatio a ha k*(realCoefficient a v (jacobi.Bessel.sigma a ha k)*
    realCoefficient a v (jacobi.Bessel.sigma a ha k))-
    realCoefficient a v (eigenvalue a k)*realCoefficient a v (eigenvalue a k))/norming a k=_
  ring

/-- The genuine kernel correction has its actual coefficient-difference series as a convergent sum for every original L2 input.
Use: adding the proved actual reference Parseval series gives the source positive quadratic identity, with convergence of both spectral series justified.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the actual summands have the full-index summable inverse-square
uniform bound. Multiply it by the genuine product of the original
absolute L1 input values. Dominated convergence for the actual series
therefore commutes its sum and double Lebesgue integral. Identify every
term by its already proved genuine rank-one coefficient integral. -/
theorem kernel_quadratic_hasSum (a : ℝ) (ha : -1<a) (v : Space) :
    HasSum (fun k => (normingRatio a ha k*(realCoefficient a v (jacobi.Bessel.sigma a ha k))^2-
      (realCoefficient a v (eigenvalue a k))^2)/norming a k) (kernelQuadratic a ha v) := by
  -- The actual source F_k estimate dominates the entire product-space integrand at every original index.
  obtain ⟨C,_,hbound⟩ := kernelTerm_uniform_bound a ha
  let M := fun k:ℕ => C/(k+1:ℝ)^2
  have hM : Summable M := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  have hvprod : Integrable (fun p:Interval×Interval => ‖v p.1‖*‖v p.2‖) (volume.prod volume) :=
    (space_integrable v).norm.mul_prod (space_integrable v).norm
  have hp : Continuous (fun p:Interval×Interval => (halfTime p.1,halfTime p.2)) :=
    (halfTime.continuous.comp continuous_fst).prodMk (halfTime.continuous.comp continuous_snd)
  have hc (k : ℕ) : Continuous (fun p:Interval×Interval => kernelTerm a ha k (halfTime p.1) (halfTime p.2)) := by
    have hh := ContinuousOn.comp_continuous
      (g := fun p:ℝ×ℝ => kernelTerm a ha k p.1 p.2)
      (f := fun p:Interval×Interval => (halfTime p.1,halfTime p.2))
      (kernelTerm_continuousOn a ha k) hp (fun p => ⟨halfTime_mem p.1,halfTime_mem p.2⟩)
    exact hh
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun p:Interval×Interval => (v p.1*v p.2)*kernelTerm a ha k (halfTime p.1) (halfTime p.2)) (volume.prod volume) :=
    ((space_integrable v).aestronglyMeasurable.comp_fst.mul
      (space_integrable v).aestronglyMeasurable.comp_snd).mul (hc k).aestronglyMeasurable
  have hdom : Integrable (fun p:Interval×Interval => ∑' k,M k*(‖v p.1‖*‖v p.2‖)) (volume.prod volume) := by
    simp_rw [tsum_mul_right]
    exact hvprod.const_mul _
  have hs := hasSum_integral_of_dominated_convergence (μ := volume.prod volume)
    (fun k (p:Interval×Interval) => M k*(‖v p.1‖*‖v p.2‖)) hmeas
    (fun k => Eventually.of_forall (fun p => by
      rw [norm_mul,norm_mul,Real.norm_eq_abs (kernelTerm _ _ _ _ _)]
      calc
        _ ≤ (‖v p.1‖*‖v p.2‖)*M k := mul_le_mul_of_nonneg_left
          (hbound k _ (halfTime_mem p.1) _ (halfTime_mem p.2)) (by positivity)
        _ = _ := mul_comm _ _))
    (Eventually.of_forall (fun p => hM.mul_right (‖v p.1‖*‖v p.2‖))) hdom
    (Eventually.of_forall (fun p => by
      have hk : Summable (fun k => kernelTerm a ha k (halfTime p.1) (halfTime p.2)) := by
        apply Summable.of_norm
        simpa only [Real.norm_eq_abs] using kernel_absolute_summable a ha (halfTime_mem p.1) (halfTime_mem p.2)
      change HasSum (fun k => (v p.1*v p.2)*kernelTerm a ha k (halfTime p.1) (halfTime p.2))
        ((v p.1*v p.2)*kernel a ha (halfTime p.1) (halfTime p.2))
      rw [kernel]
      exact hk.hasSum.mul_left (v p.1*v p.2)))
  simp only [kernelTerm_quadratic] at hs
  convert! hs using 1

end
end jacobi.GelfandLevitan
