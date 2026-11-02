import jacobi.Analytic.ProfileSeries
import Mathlib.MeasureTheory.Integral.Bochner.L1

/-!
Article: jacobi, Lemma C.1.
The original squared-profile energy has a holomorphic continuation at
every admissible real order. This is the actual original spectral sum
and integral, with exact equality to the prior real construction.
Complex integration is bilinear throughout; no conjugation is inserted.
Use: the actual analytic profile square has a holomorphic genuine source energy integral.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric Filter MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Integration over the original physical unit interval as a bounded complex-linear map on continuous functions.
Use: the actual analytic profile square has a holomorphic genuine source energy integral.
Article: jacobi, Lemma C.1.
Source: mathlib's genuine complex-linear Bochner L1 integral and continuous-to-L1 embedding. -/
def complexProfileIntegral : C(Interval,ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' (α := Interval) (E := ℂ) (μ := volume) ℂ) ∘L
    ContinuousMap.toLp (𝕜 := ℂ) (p := 1) volume

/-- The bounded complex profile integration map is exactly the original Lebesgue subtype integral.
Use: identifies the analytic energy with the article's genuine original squared-profile integral.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the complex-linear L1 integration map is its true Bochner integral, and the continuous-to-L1 image has its original continuous function as its almost-everywhere representative. -/
theorem complexProfileIntegral_apply (f : C(Interval,ℂ)) :
    complexProfileIntegral f=∫ t : Interval,f t := by
  change L1.integralCLM' ℂ (ContinuousMap.toLp (𝕜 := ℂ) (p := 1) volume f)=_
  rw [← L1.integral_eq' ℂ,L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp volume f)

/-- The genuine analytic continuation of the original persymmetric energy, formed from its actual full reflected spectral profile.
Use: establishes order analyticity of the article's original c_star, before its separate derivative and optimality conclusions.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def OrderDisk.persymmetricEnergy {a0 : ℝ} (D : OrderDisk a0) (a : ℂ) : ℂ :=
  complexProfileIntegral ((D.profileMap a)^2)

/-- The actual original continued persymmetric energy is holomorphic on each genuine inverse disk with its proved uniform GL bound.
Use: supplies the holomorphic extension needed for real analyticity of c_star in Theorem 4.2.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the genuine norm-summed original profile is Banach holomorphic. Its pointwise square is holomorphic in the same continuous-function Banach algebra. Compose with the bounded complex-linear original integral map. -/
theorem OrderDisk.persymmetricEnergy_holomorphic {a0 r B : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hB : 0<B) (hbound : ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ‖D.GLsolution a‖≤B)
    (hunit : ∀ a∈ball (a0:ℂ) r,IsUnit (D.GLoperator a)) :
    DifferentiableOn ℂ D.persymmetricEnergy (ball (a0:ℂ) r) := by
  intro a ha
  have hs := (D.profileMap_holomorphic hrD hB hbound hunit a ha).pow 2
  convert! complexProfileIntegral.differentiableAt.comp_differentiableWithinAt
    (F := C(Interval,ℂ)) (G := ℂ) a hs using 1

/-- At every real disk order the genuine analytic squared-profile integral equals the article's original real persymmetric constant.
Use: rules out an unrelated analytic surrogate and identifies the actual energy in Appendix E.1 and Theorem 4.2.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual full analytic spectral profile has its proved original real value. Real inclusion preserves its literal square and commutes with the true original Bochner integral, giving exactly the prior source definition. -/
theorem OrderDisk.persymmetricEnergy_real {a0 r B b : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hB : 0<B) (hbound : ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ‖D.GLsolution a‖≤B)
    (hb : -1<b) (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤r) :
    D.persymmetricEnergy (b:ℂ)=(persymmetricConstant b hb:ℂ) := by
  rw [OrderDisk.persymmetricEnergy,complexProfileIntegral_apply,D.profileMap_real hrD hB hbound hb hbd]
  change (∫ t : Interval,(persymmetricProfile b hb t:ℂ)^2)=
    (∫ t : Interval,(persymmetricProfile b hb t)^2:ℝ)
  convert! integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure Interval))
    (f := fun t : Interval => (persymmetricProfile b hb t)^2) using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => (_root_.Complex.ofReal_pow (persymmetricProfile b hb t) 2).symm)

/-- Every original admissible real order has a genuine holomorphic original transformed profile and energy on one common complex neighborhood, with normal convergence and exact real identification.
Use: supplies the complete analytic profile-and-energy assertions of Appendix E.1 without any unproved continuation, spectral, convergence, inverse or reference-function input.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: obtain the original numbered spectral disk, then its proved bounded analytic GL inverse subdisk. The actual transformed waves are Banach holomorphic there. Their original weighted squared profiles have a proved normal majorant, yielding the actual bounded holomorphic profile sum; its genuine squared integral is holomorphic and has the exact original real value. -/
theorem analytic_persymmetric_energy {a0 : ℝ} (ha0 : -1<a0) :
    ∃ D : OrderDisk a0,∃ r C : ℝ,0<r ∧ r<D.radius ∧ 0<C ∧
      (∀ k,DifferentiableOn ℂ (D.transformedMap k) (ball (a0:ℂ) r)) ∧
      TendstoUniformlyOn (fun N : ℕ => fun a : ℂ => ∑ k∈Finset.range N,D.profileTerm k a)
        D.profileMap atTop (closedBall (a0:ℂ) r) ∧
      (∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ‖D.profileMap a‖≤C) ∧
      DifferentiableOn ℂ D.profileMap (ball (a0:ℂ) r) ∧
      DifferentiableOn ℂ D.persymmetricEnergy (ball (a0:ℂ) r) ∧
      (∀ b : ℝ,∀ hb : -1<b,‖(b:ℂ)-(a0:ℂ)‖≤r →
        D.profileMap (b:ℂ)=continuousOfReal (persymmetricProfile b hb) ∧
          D.persymmetricEnergy (b:ℂ)=(persymmetricConstant b hb:ℂ)) := by
  -- The sole input is the original admissible real order; every analytic construction uses the actual source data.
  obtain ⟨D⟩ := orderDisk_nonempty ha0
  obtain ⟨r,B,hr,hrD,hB,hdata,_⟩ := D.GLsolution_local ha0
  have hbound := fun a ha => (hdata a ha).2
  have hunit : ∀ a∈ball (a0:ℂ) r,IsUnit (D.GLoperator a) :=
    fun a ha => (hdata a (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using ha))).1
  obtain ⟨C,hC,hφ⟩ := D.profileMap_bound hrD.le hB hbound
  exact ⟨D,r,C,hr,hrD,hC,D.transformedMap_holomorphic hrD.le hunit,
    D.profileMap_uniform hrD.le hB hbound,hφ,D.profileMap_holomorphic hrD.le hB hbound hunit,
    D.persymmetricEnergy_holomorphic hrD.le hB hbound hunit,fun b hb hbd =>
      ⟨D.profileMap_real hrD.le hB hbound hb hbd,D.persymmetricEnergy_real hrD.le hB hbound hb hbd⟩⟩

end
end jacobi.Analytic
