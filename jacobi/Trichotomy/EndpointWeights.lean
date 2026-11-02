import jacobi.Reference.NormingWeights
import jacobi.Reference.NormBounds
import jacobi.Reference.NormingBounds
import Mathlib.Analysis.PSeries

/-!
Article: jacobi, Proposition C.4.
The actual endpoint weights Lambda_k*rho_k/N_k are positive and bounded
by a constant times k^(2gamma-2). Their original sum is proved finite
in the required subcritical range gamma<1/2, where it is the positive
leading coefficient of the persymmetric profile.
Use: endpointConstant is the printed positive coefficient c_alpha in Proposition C.4.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The actual original spectral coefficient in the endpoint profile expansion.
Use: endpointConstant is the printed positive coefficient c_alpha in Proposition C.4.
Article: jacobi, Proposition C.4.
-/
def endpointWeight (a:ℝ) (ha:-1<a) (k:ℕ) : ℝ :=
  jacobi.Bessel.edgeValue a ha k*(normingRatio a ha k/norming a k)

/-- Every genuine original endpoint coefficient is strictly positive.
Use: the convergent original endpoint sum is nonzero without a numerical estimate.
Article: jacobi, Proposition C.4.
Proof: all three original spectral and norming quantities have already proved strict signs. -/
theorem endpointWeight_pos (a:ℝ) (ha:-1<a) (k:ℕ) : 0<endpointWeight a ha k :=
  mul_pos ((jacobi.Bessel.edgeValue_properties ha).1 k)
    (div_pos (normingRatio_properties ha k).2 (norming_pos ha k))

/-- The actual original endpoint weights have the required common power majorant over the complete spectrum.
Use: endpointWeight_summable obtains a genuine summable majorant for the subcritical endpoint limit of Proposition C.4.
Article: jacobi, Proposition C.4.
Proof: the actual Bessel zeros grow at least linearly, so Lambda_k is
bounded by C/k^2. The genuine rho is bounded, and the actual integral
norm N_k is at least c/k^(2gamma). Multiply these proved positive bounds. -/
theorem endpointWeight_bound (a:ℝ) (ha:-1<a) :
    ∃C:ℝ,0<C ∧ ∀k:ℕ,endpointWeight a ha k≤C*(k+1:ℝ)^(2*gamma a-2) := by
  -- Both the finite low-frequency prefix and the infinite tail are controlled by proved all-index original bounds.
  obtain ⟨cZ,_,hcZ,_,hZ⟩ := jacobi.Bessel.positiveZero_linear_bounds ha
  obtain ⟨cN,_,hcN,_,hN⟩ := norming_bounds ha
  obtain ⟨_,R,_,_,hR,_,hρ⟩ := normingRatio_bounds ha
  refine ⟨2*R/(cZ^2*cN),by positivity,fun k => ?_⟩
  have hk : 0<(k+1:ℝ) := by positivity
  have hp : 0<(k+1:ℝ)^(2*gamma a) := Real.rpow_pos_of_pos hk _
  have hsig : cZ^2*(k+1:ℝ)^2≤ jacobi.Bessel.sigma a ha k := by
    rw [← (jacobi.Bessel.positiveZero_properties ha k).2]
    have hh := (sq_le_sq₀ (mul_pos hcZ hk).le (jacobi.Bessel.positiveZero_properties ha k).1.le).mpr (hZ k).1
    nlinarith [hh]
  have hvalue : jacobi.Bessel.edgeValue a ha k≤2/(cZ^2*(k+1:ℝ)^2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hsig
  have hW : normingRatio a ha k/norming a k≤R/(cN/(k+1:ℝ)^(2*gamma a)) :=
    div_le_div₀ hR.le (hρ k).2.1 (by positivity) (hN k).1
  have hb := mul_le_mul hvalue hW
    (div_pos (normingRatio_properties ha k).2 (norming_pos ha k)).le (by positivity)
  apply hb.trans_eq
  rw [Real.rpow_sub hk,Real.rpow_two]
  field_simp

/-- The actual endpoint coefficient series is genuinely summable in the complete compact-support regime.
Use: endpoint_profile_limit interchanges the true spatial endpoint limit with the unchanged full original spectral series.
Article: jacobi, Proposition C.4.
Proof: the proved exponent 2gamma-2 is strictly less than minus one.
The community p-series theorem sums its original positive-index power
majorant, which dominates every actual positive endpoint coefficient. -/
theorem endpointWeight_summable (a:ℝ) (ha:-1<a) (hsub:a < -(1/2:ℝ)) :
    Summable (endpointWeight a ha) := by
  obtain ⟨C,hC,hbound⟩ := endpointWeight_bound a ha
  have hexp : 2*gamma a-2 < -1 := by dsimp only [gamma]; linarith
  have hs := (Real.summable_nat_rpow.mpr hexp).comp_injective
    (show Function.Injective (fun k:ℕ => k+1) from fun i j h => Nat.add_right_cancel h)
  have hsm : Summable (fun k:ℕ => C*(k+1:ℝ)^(2*gamma a-2)) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using hs.mul_left C
  exact hsm.of_nonneg_of_le (fun k => (endpointWeight_pos a ha k).le) hbound

/-- The source's leading endpoint constant is the actual complete spectral sum.
Use: endpointConstant_pos and endpoint_profile_limit give its finite positive value and the source's exact endpoint asymptotic.
Article: jacobi, Proposition C.4.
-/
def endpointConstant (a:ℝ) (ha:-1<a) : ℝ := ∑'k,endpointWeight a ha k

/-- The actual convergent endpoint constant is strictly positive throughout the original compact-support regime.
Use: the compact-support tail and inverse packing coordinate have the genuine required positive leading coefficient.
Article: jacobi, Proposition C.4.
Proof: the first positive original endpoint coefficient is bounded by its genuinely summable positive series. -/
theorem endpointConstant_pos (a:ℝ) (ha:-1<a) (hsub:a < -(1/2:ℝ)) : 0<endpointConstant a ha :=
  (endpointWeight_pos a ha 0).trans_le ((endpointWeight_summable a ha hsub).le_tsum 0
    (fun k _ => (endpointWeight_pos a ha k).le))

end
end jacobi.Trichotomy
