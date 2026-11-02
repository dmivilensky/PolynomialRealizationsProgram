import jacobi.Analytic.TransformedSpectralMaps
import jacobi.GelfandLevitan.Profiles

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The literal continued Lambda-weighted squared profiles are holomorphic
continuous functions on the original reflected physical interval. Their
full-index norms have a common summable inverse-square majorant.
Use: its normally convergent sum is the original analytic persymmetric profile and defines c_star.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric jacobi.Reference jacobi.GelfandLevitan jacobi.ComplexReference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual continued original Lambda-weighted squared spectral profile, with its prescribed reflection extension.
Use: its normally convergent sum is the original analytic persymmetric profile and defines c_star.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def OrderDisk.profileTerm {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) (a : ℂ) : C(Interval,ℂ) :=
  (2*D.normingRatio k a/(D.spectrum k a*norming a k)) •
    ((D.transformedMap k a)^2).comp physicalFold

/-- The genuine profile-term coefficient is holomorphic on the common order disk, with every original denominator proved nonzero.
Use: the actual Lambda-weighted profile terms are holomorphic continuous-function vectors.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the original spectrum, norming product and reference norm quotient are holomorphic. The genuine quadratic spectral lower bound and positive-exponent norming formula make both original denominator factors nonzero. -/
theorem OrderDisk.profileCoefficient_holomorphic {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) :
    DifferentiableOn ℂ (fun a => 2*D.normingRatio k a/(D.spectrum k a*norming a k))
      (ball (a0:ℂ) D.radius) := by
  -- No branch or sign choice is used in the original bilinear coefficient.
  intro a ha
  have had : ‖a-(a0:ℂ)‖≤D.radius := le_of_lt (by simpa only [mem_ball,dist_eq_norm] using ha)
  have hag : 0<(gamma a).re := by have har := D.admissible had; unfold jacobi.ComplexReference.gamma; norm_num; linarith
  have hS := ((D.holomorphic k).mono (ball_subset_ball (by linarith [D.radius_pos]))) a ha
  have hN := (norming_comp_analytic analyticAt_id hag k).differentiableAt.differentiableWithinAt
    (s := ball (a0:ℂ) D.radius)
  have hSne : D.spectrum k a≠0 := norm_pos_iff.mp
    ((mul_pos D.gap_pos (by positivity : (0:ℝ)<(k+1:ℝ)^2)).trans_le (D.lower a had k))
  exact ((differentiableWithinAt_const (c := (2:ℂ))).mul (D.normingRatio_holomorphic k a ha)).div
    (hS.mul hN) (mul_ne_zero hSne (norming_ne_zero hag k))

/-- The original continued Lambda-weighted profile terms are holomorphic in the whole-interval continuous-function norm on every genuine inverse subdisk.
Use: the normal profile series is holomorphic as a continuous function and its actual squared integral is holomorphic.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the genuine transformed spectral vector is norm holomorphic, as are its pointwise square and bounded reflection precomposition. Multiply by the proved actual holomorphic nonzero-denominator coefficient. -/
theorem OrderDisk.profileTerm_holomorphic {a0 r : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hunit : ∀ a∈ball (a0:ℂ) r,IsUnit (D.GLoperator a)) (k : ℕ) :
    DifferentiableOn ℂ (D.profileTerm k) (ball (a0:ℂ) r) := by
  -- Reflection is the same bounded physical precomposition used by the original real profiles.
  intro a ha
  have hu := (D.transformedMap_holomorphic hrD hunit k a ha).pow 2
  have hc := (ContinuousMap.compCLM ℂ ℂ physicalFold).differentiableAt.comp_differentiableWithinAt
    (F := C(HalfInterval,ℂ)) (G := C(Interval,ℂ)) a hu
  exact ((D.profileCoefficient_holomorphic k).mono (ball_subset_ball hrD) a ha).smul hc

/-- Every original continued profile term has one common inverse-square norm bound on any closed inverse disk with its proved uniform GL bound.
Use: gives genuine absolute and uniform convergence of the analytic persymmetric profile, including every finite original spectral index.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual spectral denominator is at least a positive constant times the squared index. The reference norm has the same squared amplitude scale as the genuine transformed solution. Cancel those matching powers, use the actual common norming-product bound, and retain precisely the inverse-square spectral factor. -/
theorem OrderDisk.profileTerm_bounds {a0 r B : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hB : 0<B) (hbound : ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ‖D.GLsolution a‖≤B) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ∀ k : ℕ,
      ‖D.profileTerm k a‖≤C/(k+1:ℝ)^2 := by
  -- All matching index powers come from the same original reference normalization and true transformed solution.
  obtain ⟨A,hA,hU⟩ := D.transformedMap_bounds hrD hB hbound
  obtain ⟨R,hR,hρ⟩ := D.normingRatio_bounds
  obtain ⟨c,_,hc,_,hN⟩ := norming_bounds (isCompact_closedBall (a0:ℂ) D.radius) (by
    intro a ha
    have har := D.admissible (by simpa only [mem_closedBall,dist_eq_norm] using ha)
    unfold jacobi.ComplexReference.gamma
    norm_num
    linarith)
  refine ⟨2*R*A^2/(D.gapConstant*c),by have hg := D.gap_pos; positivity,fun a ha k => ?_⟩
  have had := ha.trans hrD
  have hkp : 0<(k+1:ℝ) := by positivity
  let p : ℝ := (k+1:ℝ)^(-(gamma a).re)
  have hp : 0<p := Real.rpow_pos_of_pos hkp _
  have hpsq : p^2=1/(k+1:ℝ)^(2*(gamma a).re) := by
    dsimp [p]
    rw [Real.rpow_neg hkp.le,show 2*(gamma a).re=(gamma a).re*2 by ring,
      Real.rpow_mul hkp.le,Real.rpow_two,inv_pow,one_div]
  have hNorm : c*p^2≤‖norming a k‖ := by
    rw [hpsq]
    simpa only [mul_one_div] using (hN a (by simpa only [mem_closedBall,dist_eq_norm] using had) k).1
  have hDen : (D.gapConstant*(k+1:ℝ)^2)*(c*p^2)≤‖D.spectrum k a*norming a k‖ := by
    rw [norm_mul]
    exact mul_le_mul (D.lower a had k) hNorm (by positivity) (norm_nonneg _)
  apply (ContinuousMap.norm_le _ (by have hg := D.gap_pos; positivity)).mpr
  intro t
  have hUval : ‖D.transformedMap k a (physicalFold t)‖≤A*p := by
    exact ((D.transformedMap k a).norm_coe_le_norm _).trans (by
      simpa only [p,Real.rpow_neg hkp.le,div_eq_mul_inv] using hU a ha k)
  have hρval := (hρ a had k).1
  change ‖(2*D.normingRatio k a/(D.spectrum k a*norming a k))*
    (D.transformedMap k a (physicalFold t))^2‖≤_
  rw [div_mul_eq_mul_div,norm_div]
  have hnum : ‖2*D.normingRatio k a*(D.transformedMap k a (physicalFold t))^2‖≤2*R*(A*p)^2 := by
    rw [norm_mul,norm_mul,norm_pow]
    rw [show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hρval (by norm_num : (0:ℝ)≤2))
      (pow_le_pow_left₀ (norm_nonneg _) hUval 2) (by positivity) (by positivity)
  have hpos : 0<(D.gapConstant*(k+1:ℝ)^2)*(c*p^2) := by have hg := D.gap_pos; positivity
  have hh := div_le_div₀ (show 0≤2*R*(A*p)^2 by positivity) hnum hpos hDen
  exact hh.trans_eq (by field_simp [hc.ne',hp.ne',hkp.ne',D.gap_pos.ne'])

/-- At real disk orders every actual continued profile term is exactly the original Lambda-weighted reflected spectral profile.
Use: the analytic profile series and its squared integral retain the article's genuine original real normalization.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the genuine numbered spectrum, norming product, reference norm and transformed wave all have their proved original real values. Substitute them in the same literal bilinear squared-profile formula and use the original Lambda_k=2/sigma_k. -/
theorem OrderDisk.profileTerm_real {a0 b : ℝ} (D : OrderDisk a0) (hb : -1<b)
    (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤D.radius) (k : ℕ) (t : Interval) :
    D.profileTerm k (b:ℂ) t=
      (jacobi.Bessel.edgeValue b hb k* jacobi.GelfandLevitan.spectralProfile b hb k t:ℂ) := by
  -- The actual reflection extension and every spectral coefficient are retained term by term.
  change (2*D.normingRatio k (b:ℂ)/(D.spectrum k (b:ℂ)* jacobi.ComplexReference.norming (b:ℂ) k))*
    (D.transformedMap k (b:ℂ) (physicalFold t))^2=_
  rw [D.normingRatio_real hb hbd k,D.real_eq b hb hbd k,jacobi.ComplexReference.norming_real hb k,
    D.transformedMap_real hb hbd k (physicalFold t),← realTransformedSolution_cast]
  change _ = (((2:ℝ)/ jacobi.Bessel.sigma b hb k:ℝ):ℂ)*
    (((jacobi.Reference.normingRatio b hb k/ jacobi.Reference.norming b k)*
      (realTransformedSolution b hb (jacobi.Bessel.sigma b hb k) (physicalFold t))^2:ℝ):ℂ)
  push_cast
  simp only [div_eq_mul_inv,mul_inv]
  ring

end
end jacobi.Analytic
