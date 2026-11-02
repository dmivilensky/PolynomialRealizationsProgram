import jacobi.RootMass.Needle
import jacobi.Variational.Congruence

/-!
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
The existing exact quadratic spectral expansion is applied to genuine
finite-interval replacements. Lebesgue primitive derivatives identify the
linear Green term; the proved L1 bound makes the actual remainder have zero
right derivative. No spectral expansion or o(epsilon) term is postulated.
Source: the proved signed second-moment expansion and Lebesgue differentiation.
Use: gives a common Lebesgue derivative set for the true spectral needle linear term.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original density times its actual Green potential is integrable on the full line.
Use: gives a common Lebesgue derivative set for the true spectral needle linear term.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the actual continuous potential is bounded by mass, so multiply the L1 density by this bounded measurable function. -/
theorem RootDensity.potential_product_integrable (m : RootDensity) :
    Integrable (fun x => m.value x*potential m.toDensity x) := by
  apply m.integrable.mul_bdd (potential_continuous m.toDensity).1.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (potential_nonneg m.toDensity x)]
    exact potential_le_mass m.toDensity x

/-- The actual needle Green pairing is exactly the difference of its two interval primitives.
Use: the original Lebesgue primitive derivatives identify its first-order variation.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: apply the proved actual signed convolution pairing and split its two absolutely integrable terms. -/
theorem RootDensity.needle_pairing_interval (m : RootDensity) (z : ℝ) (hz : 0≤z) (x eps : ℝ) (heps : 0≤eps) :
    secondPairing m.value ((m.needle z hz x eps).value-m.value)=
      z*(∫ t in x..x+eps,potential m.toDensity t)-∫ t in x..x+eps,m.value t*potential m.toDensity t := by
  have hW : IntegrableOn (potential m.toDensity) (Ioc x (x+eps)) volume :=
    ((potential_continuous m.toDensity).1.intervalIntegrable x (x+eps)).1
  rw [m.needle_pairing]
  simp_rw [sub_mul]
  rw [integral_sub (hW.const_mul z) m.potential_product_integrable.integrableOn,
    integral_const_mul,← intervalIntegral.integral_of_le (by linarith : x≤x+eps),
    ← intervalIntegral.integral_of_le (by linarith : x≤x+eps)]

/-- The genuine actual spectral needle has the source's exact first derivative at every common primitive point.
Use: the normalized admissible needle proves the pointwise minimum principle with every spectral remainder discharged.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the localized actual Green pairing differentiates by the three true
primitive derivatives. The exact quadratic remainder is bounded by the
square of the vanishing mass primitive, so its right derivative is zero.
Recombine the original spectral expansion to obtain the actual spectral derivative. -/
theorem RootDensity.needle_spectral_derivative (m : RootDensity) (z : ℝ) (hz : 0≤z) (x : ℝ)
    (hm : HasDerivAt (fun v => ∫ t in x..v,m.value t) (m.value x) x)
    (hW : HasDerivAt (fun v => ∫ t in x..v,potential m.toDensity t) (potential m.toDensity x) x)
    (hmW : HasDerivAt (fun v => ∫ t in x..v,m.value t*potential m.toDensity t)
      (m.value x*potential m.toDensity x) x) :
    HasDerivWithinAt (fun eps => observe (m.needle z hz x eps).toDensity .second)
      (2*potential m.toDensity x*(z-m.value x)) (Ici (0:ℝ)) 0 := by
  -- The remainder and linear term are defined by the genuine original spectral observation.
  let L (eps : ℝ) := z*eps+∫ t in x..x+eps,m.value t
  let H (eps : ℝ) := secondPairing m.value ((m.needle z hz x eps).value-m.value)
  let R (eps : ℝ) := observe (m.needle z hz x eps).toDensity .second-observe m.toDensity .second-2*H eps
  have hG0 : observe (m.needle z hz x 0).toDensity .second=observe m.toDensity .second :=
    observe_congr (Eventually.of_forall fun t => congrFun (m.needle_zero_value z hz x) t) .second
  have hH0 : H 0=0 := by
    dsimp only [H]
    rw [m.needle_zero_value,sub_self]
    simp [secondPairing]
  have hR0 : R 0=0 := by dsimp only [R]; rw [hG0,hH0]; ring
  have hL0 : L 0=0 := by simp [L]
  have hLd : HasDerivAt L (z+m.value x) 0 := by
    convert ((hasDerivAt_id 0).const_mul z).add (translated_primitive_derivative hm) using 1
    · rfl
    · simp
  have hRb (eps : ℝ) (heps : 0≤eps) : |R eps|≤(L eps)^2 := by
    have hb := second_expansion_remainder m.toL1Source (m.needle z hz x eps).toL1Source
    have hdist := m.needle_distance z hz x eps heps
    have hd0 : 0≤∫ t,|(m.needle z hz x eps).value t-m.value t| := integral_nonneg (fun _ => abs_nonneg _)
    exact hb.trans ((sq_le_sq₀ hd0 (hd0.trans hdist)).mpr hdist)
  have hRd := quadratic_remainder hR0 hL0 hLd hRb
  have hHd : HasDerivWithinAt H (z*potential m.toDensity x-m.value x*potential m.toDensity x) (Ici (0:ℝ)) 0 := by
    have hp := ((translated_primitive_derivative hW).const_mul z).sub (translated_primitive_derivative hmW)
    apply hp.hasDerivWithinAt.congr_of_eventuallyEq_of_mem _ (by simp)
    filter_upwards [self_mem_nhdsWithin] with eps heps
    exact m.needle_pairing_interval z hz x eps heps
  convert (hasDerivWithinAt_const (0:ℝ) (Ici (0:ℝ)) (observe m.toDensity .second)).add
    ((hHd.const_mul 2).add hRd) using 1
  · funext eps
    dsimp only [R,Pi.add_apply,Pi.mul_apply]
    ring
  · ring

end
end jacobi.RootMass
