import jacobi.GelfandLevitan.PrefixIntegral
import jacobi.GelfandLevitan.DerivativeForcing
import Mathlib.MeasureTheory.Integral.Bochner.L1

/-!
Article: jacobi, Proposition 2.2.
A continuous Banach-valued integrand averaged over a shrinking
physical interval has its genuine diagonal limit. Rescaling to the
unchanged unit interval gives this as ordinary uniform-norm continuity,
including a parameter in the integrand. It applies to K(u,r)*F(r,.).
Use: affineAverage is a continuous Banach-valued average, so the actual shrinking GL tail integral has a true uniform-norm limit.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- Integration of a genuine continuous row over the original unit interval, as a bounded linear map.
Use: affineAverage is a continuous Banach-valued average, so the actual shrinking GL tail integral has a true uniform-norm limit.
Article: jacobi, Proposition 2.2.
Source: the community continuous-to-L1 embedding and the Bochner integral continuous linear map. -/
def unitRowIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] :
    C(Interval,E) →L[ℝ] E :=
  L1.integralCLM ∘L ContinuousMap.toLp (𝕜 := ℝ) (p := 1) volume

/-- The bounded unit-row integration map is precisely the original subtype Lebesgue integral.
Use: the uniform-norm continuous average is identified with the literal rescaled shrinking original GL integral.
Article: jacobi, Theorem 2.1.
Proof: the community Bochner L1 integration map is its actual integral, and the continuous-to-L1 vector has the original continuous row as its genuine almost-everywhere representative. -/
theorem unitRowIntegral_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : C(Interval,E)) : unitRowIntegral g=∫ x : Interval,g x := by
  change L1.integralCLM (ContinuousMap.toLp (𝕜 := ℝ) (p := 1) volume g)=_
  rw [← L1.integral_eq,L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp volume g)

/-- The genuine affine point between two original physical coordinates at a unit-interval parameter.
Use: rescaling a shrinking physical interval remains within the unchanged original physical half domain, so only the proved continuous original integrand is used.
Article: jacobi, Theorem 2.1.
-/
def halfInterpolate : C((HalfInterval×HalfInterval)×Interval,HalfInterval) :=
  ⟨fun p => ⟨(1-(p.2:ℝ))*(p.1.1:ℝ)+(p.2:ℝ)*(p.1.2:ℝ),by
    have h0 := sub_nonneg.mpr p.2.property.2
    refine ⟨add_nonneg (mul_nonneg h0 p.1.1.property.1) (mul_nonneg p.2.property.1 p.1.2.property.1),?_⟩
    have h := add_le_add (mul_le_mul_of_nonneg_left p.1.1.property.2 h0)
      (mul_le_mul_of_nonneg_left p.1.2.property.2 p.2.property.1)
    linarith⟩,
    by fun_prop⟩

/-- Continuous real-parameter clipping to the original physical half interval.
Use: the normalized shrinking physical integral has an explicit continuous real-coordinate extension, while every integration point between its true endpoints remains unchanged.
Article: jacobi, Theorem 2.1.
-/
def halfParameterClamp : C(ℝ,HalfInterval) :=
  ⟨Set.projIcc (0:ℝ) (1/2) (by norm_num),continuous_projIcc⟩

/-- Integration over the actual unit subtype equals the unchanged real unit-interval integral.
Use: affineAverage_integral rescales the genuine shrinking original GL integral to its continuous unit-domain average.
Article: jacobi, Theorem 2.1.
Proof: the already proved original prefix-integral identity at t=1 has the entire genuine unit subtype as its physical prefix. -/
theorem unit_subtype_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℝ → E) : (∫ x : Interval,g (x:ℝ))=∫ x in (0:ℝ)..1,g x := by
  have h := prefix_integral g (t := 1) (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1)
  have hp : prefixSet 1=univ := Set.eq_univ_of_forall (fun x => x.property.2)
  simpa only [hp,setIntegral_univ] using h

/-- The actual average of a continuous parameter-dependent original integrand along the physical segment from t to u.
Use: shrinkingIntegral_limit applies continuity of this genuine compact-domain Banach average at u=t to the moving-upper-endpoint GL forcing.
Article: jacobi, Theorem 2.1.
-/
def affineAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : C(HalfInterval×HalfInterval,E)) (t : HalfInterval) : C(HalfInterval,E) :=
  let P : C(HalfInterval×Interval,HalfInterval×HalfInterval) :=
    ⟨fun p => (p.1,halfInterpolate ((t,p.1),p.2)),
      continuous_fst.prodMk (halfInterpolate.continuous.comp
        ((continuous_const.prodMk continuous_fst).prodMk continuous_snd))⟩
  ⟨fun u => unitRowIntegral ((H.comp P).curry u),unitRowIntegral.continuous.comp (H.comp P).curry.continuous⟩

/-- At the genuine collapsed interval, the continuous original affine average equals its actual diagonal integrand.
Use: affineAverage_tendsto fixes the exact limit of the shrinking original GL tail as K(t,t)*F(t,.), including its original normalization.
Article: jacobi, Theorem 2.1.
Proof: the affine physical point equals t at both equal endpoints; the genuine unit interval has total measure one, so its actual constant integral equals that same value. -/
theorem affineAverage_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : C(HalfInterval×HalfInterval,E)) (t : HalfInterval) : affineAverage H t t=H (t,t) := by
  -- The diagonal identity retains the unit physical measure, rather than a hidden change of normalization.
  change unitRowIntegral _=_
  rw [unitRowIntegral_apply]
  have hp (x : Interval) : halfInterpolate ((t,t),x)=t := by
    apply Subtype.ext
    dsimp [halfInterpolate]
    ring
  simp only [ContinuousMap.curry_apply,ContinuousMap.comp_apply,ContinuousMap.coe_mk,hp]
  rw [integral_const,Measure.real,interval_volume_univ]
  simp only [ENNReal.toReal_one,one_smul]

/-- The original parameter-dependent physical averages converge in their actual Banach norm to the genuine diagonal value.
Use: the GL difference-quotient forcing has exactly the same uniform-norm tail limit; the original forced inverse continuity then identifies the true derivative of K.
Article: jacobi, Theorem 2.1.
Proof: the actual affine average is already a continuous map in its unchanged Banach norm, and its collapsed-interval value is independently evaluated exactly. -/
theorem affineAverage_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : C(HalfInterval×HalfInterval,E)) (t : HalfInterval) :
    Tendsto (affineAverage H t) (𝓝 t) (𝓝 (H (t,t))) := by
  simpa only [affineAverage_self] using (affineAverage H t).continuous.continuousAt.tendsto (x := t)

/-- The actual original affine average is exactly the normalized original shrinking physical integral whenever its endpoints differ.
Use: the genuine GL moving-boundary forcing is identified with affineAverage, whose Banach-norm diagonal limit has already been proved.
Article: jacobi, Theorem 2.1.
Proof: the physical affine interpolation remains in the original half interval, so its explicit real-coordinate clamp is the same point. Convert the genuine unit subtype integral to the original real unit integral and apply the community affine interval substitution theorem. -/
theorem affineAverage_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : C(HalfInterval×HalfInterval,E)) (t u : HalfInterval) (htu : u≠t) :
    affineAverage H t u=((u:ℝ)-(t:ℝ))⁻¹ •
      (∫ r in (t:ℝ)..(u:ℝ),H (u,halfParameterClamp r)) := by
  -- The original parameter-dependent integrand is unchanged throughout the entire genuine physical segment.
  have hneq : (u:ℝ)-(t:ℝ)≠0 := sub_ne_zero.mpr (fun h => htu (Subtype.ext h))
  have hp (x : Interval) : halfInterpolate ((t,u),x)=halfParameterClamp (((u:ℝ)-(t:ℝ))*(x:ℝ)+(t:ℝ)) := by
    have hval : ((halfInterpolate ((t,u),x)):ℝ)=((u:ℝ)-(t:ℝ))*(x:ℝ)+(t:ℝ) := by
      dsimp [halfInterpolate]
      ring
    have hm : ((u:ℝ)-(t:ℝ))*(x:ℝ)+(t:ℝ)∈Icc (0:ℝ) (1/2) := hval ▸ (halfInterpolate ((t,u),x)).property
    apply Subtype.ext
    change _=((Set.projIcc (0:ℝ) (1/2) (by norm_num) (((u:ℝ)-(t:ℝ))*(x:ℝ)+(t:ℝ))):ℝ)
    rw [Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1/2) hm]
    exact hval
  change unitRowIntegral _=_
  rw [unitRowIntegral_apply]
  change (∫ x : Interval,H (u,halfInterpolate ((t,u),x)))=_
  simp_rw [hp]
  rw [unit_subtype_integral (fun x : ℝ => H (u,halfParameterClamp (((u:ℝ)-(t:ℝ))*x+(t:ℝ))))]
  have h := intervalIntegral.integral_comp_mul_add (fun r : ℝ => H (u,halfParameterClamp r))
    (a := 0) (b := 1) hneq (t:ℝ)
  simpa only [mul_zero,zero_add,mul_one,sub_add_cancel] using h

end
end jacobi.GelfandLevitan
