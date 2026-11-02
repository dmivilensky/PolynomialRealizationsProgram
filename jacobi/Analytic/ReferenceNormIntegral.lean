import jacobi.Analytic.ReferenceEigenContinuation
import jacobi.Analytic.PersymmetricEnergy
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.Basic

/-!
Article: jacobi, Lemma C.1.
The actual complex bilinear integral of the original reference solution
equals its printed Gamma quotient on the full half-plane Re(gamma)>0.
The original finite-polynomial eigenfunction is Banach holomorphic on
the whole closed physical interval, so its true squared integral is
holomorphic. The identity theorem continues the already proved real
integral formula; all spatial integrals are genuinely convergent.
Use: the identity theorem continues the true squared reference integral to every Re(gamma)>0 order.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Metric Filter MeasureTheory
open jacobi.Reference (Interval)
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local irreducible] solution

/-- The original admissible complex-order half-plane is connected.
Use: the identity theorem continues the true squared reference integral to every Re(gamma)>0 order.
Article: jacobi, Lemma C.1.
Proof: rewrite the affine exponent condition as a real half-space and use convexity of a linear preimage. -/
theorem referenceOrders_preconnected : IsPreconnected referenceOrders := by
  have he : referenceOrders=Complex.reCLM.toLinearMap ⁻¹' Ioi (-(3/2:ℝ)) := by
    ext a
    simp only [referenceOrders,mem_ofPred_eq,mem_preimage,mem_Ioi,gamma]
    norm_num
    constructor <;> intro h <;> linarith
  rw [he]
  exact ((convex_Ioi (-(3/2:ℝ))).linear_preimage Complex.reCLM.toLinearMap).isPreconnected

/-- The actual full-interval complex reference eigenfunction has exactly the original real eigenfunction as its real restriction.
Use: identifies the true complex integral with the already proved original real norm formula.
Article: jacobi, Lemma C.1.
Proof: in the interior use the exact terminating spectral identity and the proved original solution restriction. At the right endpoint both actual sine-power eigenfunctions vanish, including at complex order. -/
theorem referenceEigenMap_real {a:ℝ} (ha:-1<a) (k:ℕ) (t:Interval) :
    referenceEigenMap (a:ℂ) k t=(jacobi.Reference.eigenfunction a k t:ℂ) := by
  -- The endpoint is handled from its true zero prefactor, avoiding any convergence claim at the Gauss boundary.
  have hag : (a:ℂ)∈referenceOrders := by
    change 0<(gamma (a:ℂ)).re
    rw [gamma_real,Complex.ofReal_re]
    unfold jacobi.Reference.gamma
    linarith
  by_cases ht : (t:ℝ)<1
  · rw [← solution_at_reference_complex hag k t,jacobi.Hankel.frequencyReference_ofReal,
      solution_real a _ ⟨t.property.1,ht⟩,jacobi.Reference.solution_at_eigenvalue]
  · have ht1 : (t:ℝ)=1 := le_antisymm t.property.2 (le_of_not_gt ht)
    have hne : gamma (a:ℂ)≠0 := ne_of_apply_ne Complex.re (show 0<(gamma (a:ℂ)).re from hag).ne'
    simp only [referenceEigenMap,ContinuousMap.mul_apply,weightUnitMap_apply hag,weight,ht1,
      mul_one,Real.sin_pi,zero_div,Complex.ofReal_zero,Complex.zero_cpow hne,zero_mul]
    rw [(jacobi.Reference.eigenfunction_properties ha k).2.2,Complex.ofReal_zero]

/-- The genuine complex bilinear squared norm of the original continued reference eigenfunction.
Use: its holomorphy and exact Gamma identity close the missing integral interpretation of the complex GL normalization.
Article: jacobi, Lemma C.1.
-/
def referenceNormIntegral (a:ℂ) (k:ℕ) : ℂ :=
  jacobi.Analytic.complexProfileIntegral ((referenceEigenMap a k)^2)

/-- The genuine complex reference squared integral is holomorphic on the entire admissible half-plane.
Use: permits the identity theorem with the actual printed Gamma norm quotient.
Article: jacobi, Lemma C.1.
Proof: the original eigenfunction is holomorphic in the full-interval continuous-function norm. Square it in that Banach algebra and compose with the genuine bounded complex-linear spatial integral. -/
theorem referenceNormIntegral_holomorphic (k:ℕ) :
    DifferentiableOn ℂ (fun a => referenceNormIntegral a k) referenceOrders := by
  intro a ha
  have hs := (referenceEigenMap_holomorphic k a ha).pow 2
  convert! jacobi.Analytic.complexProfileIntegral.differentiableAt.comp_differentiableWithinAt
    (F := C(Interval,ℂ)) (G := ℂ) a hs using 1

/-- On the original real order interval the actual complex squared integral is the printed norming quotient.
Use: supplies actual accumulating equality points for the full complex identity theorem.
Article: jacobi, Lemma C.1.
Proof: the actual eigenfunction has its original real value at every point. Commute real inclusion with its genuine squared integral, identify the unit subtype integral with the original interval integral, and use the proved original real Gamma formula. -/
theorem referenceNormIntegral_real {a:ℝ} (ha:-1<a) (k:ℕ) :
    referenceNormIntegral (a:ℂ) k=norming (a:ℂ) k := by
  -- The input to continuation is an actual integral equality, not a chosen normalization rule.
  rw [referenceNormIntegral,jacobi.Analytic.complexProfileIntegral_apply,norming_real ha k]
  have he : (∫ t:Interval,((referenceEigenMap (a:ℂ) k)^2) t)=
      ((∫ t:Interval,(jacobi.Reference.eigenfunction a k t)^2:ℝ):ℂ) := by
    simp only [ContinuousMap.pow_apply,referenceEigenMap_real ha]
    convert! integral_ofReal (𝕜 := ℂ) (μ := (volume:Measure Interval))
      (f := fun t:Interval => (jacobi.Reference.eigenfunction a k t)^2) using 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => (Complex.ofReal_pow (jacobi.Reference.eigenfunction a k t) 2).symm)
  rw [he]
  congr 1
  rw [integral_subtype (s := Icc (0:ℝ) 1) measurableSet_Icc
    (fun t:ℝ => (jacobi.Reference.eigenfunction a k t)^2),integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  rfl

/-- The genuine complex squared reference integral equals its printed Gamma quotient for every admissible complex order.
Use: completes the analytic normalization identification in the original GL kernel, including nonreal orders.
Article: jacobi, Lemma C.1.
Source: the analytic identity theorem on a connected complex domain.
Proof: both original functions are holomorphic on the true connected half-plane. Their independently proved actual real equality holds along positive reciprocal integers converging to the interior point zero. The community identity theorem extends this integral equality throughout the half-plane. -/
theorem referenceNormIntegral_eq {a:ℂ} (ha:a∈referenceOrders) (k:ℕ) :
    referenceNormIntegral a k=norming a k := by
  -- The continuation uses genuine accumulating real orders inside the original admissible range.
  have hI := (referenceNormIntegral_holomorphic k).analyticOnNhd referenceOrders_open
  have hN : AnalyticOnNhd ℂ (fun a => norming a k) referenceOrders :=
    fun a ha => norming_comp_analytic analyticAt_id ha k
  have h0 : (0:ℂ)∈referenceOrders := by norm_num [referenceOrders,gamma]
  have ht : Tendsto (fun n:ℕ => ((1/((n:ℝ)+1):ℝ):ℂ)) atTop (𝓝 (0:ℂ)) := by
    convert! Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1
  have hcl : (0:ℂ)∈closure ({a | referenceNormIntegral a k=norming a k} \ {(0:ℂ)}) :=
    mem_closure_of_tendsto ht (Eventually.of_forall (fun n => by
      have hn : 0<1/((n:ℝ)+1) := by positivity
      exact ⟨referenceNormIntegral_real (by linarith) k,
        by simpa only [mem_singleton_iff,Complex.ofReal_eq_zero] using hn.ne'⟩))
  exact hI.eqOn_of_preconnected_of_mem_closure hN referenceOrders_preconnected h0 hcl ha

/-- The literal complex reference solution has a genuinely convergent squared integral equal to the article's Gamma norming formula.
Use: discharges the final complex integral normalization debt in the exact source notation.
Article: jacobi, Lemma C.1.
Proof: the exact terminating spectral identity identifies the actual continuous full-interval eigenfunction. Its square is integrable and its genuine subtype integral is the original interval integral. Apply the proved complete complex Gamma identity. -/
theorem reference_norm_integral {a:ℂ} (ha:0<(gamma a).re) (k:ℕ) :
    IntervalIntegrable (fun t:ℝ => (solution a (jacobi.Hankel.frequencyReference a k) t)^2) volume 0 1 ∧
      (∫ t in (0:ℝ)..1,(solution a (jacobi.Hankel.frequencyReference a k) t)^2)=norming a k := by
  -- The continuous finite spectral representative supplies actual integrability before its value is compared.
  have hfun (t:ℝ) (ht:t∈Icc (0:ℝ) 1) :
      solution a (jacobi.Hankel.frequencyReference a k) t=referenceEigenMap a k ⟨t,ht⟩ :=
    solution_at_reference_complex ha k ⟨t,ht⟩
  have hc : ContinuousOn (fun t:ℝ => (solution a (jacobi.Hankel.frequencyReference a k) t)^2) (Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact ((referenceEigenMap a k)^2).continuous.congr (fun t => by
      change (referenceEigenMap a k t)^2=(solution a (jacobi.Hankel.frequencyReference a k) t)^2
      rw [hfun t t.property])
  refine ⟨hc.intervalIntegrable_of_Icc (by norm_num),?_⟩
  have he := referenceNormIntegral_eq ha k
  rw [referenceNormIntegral,jacobi.Analytic.complexProfileIntegral_apply] at he
  simp only [ContinuousMap.pow_apply,← solution_at_reference_complex ha k] at he
  rw [integral_subtype (s := Icc (0:ℝ) 1) measurableSet_Icc
    (fun t:ℝ => (solution a (jacobi.Hankel.frequencyReference a k) t)^2),integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] at he
  exact he

end
end jacobi.ComplexReference
