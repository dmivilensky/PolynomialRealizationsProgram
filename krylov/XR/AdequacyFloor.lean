import krylov.XR.AlgorithmModel
import krylov.Completion.Clipping

/-!
Article: main_krylov, prop:floor, the actual clipped adequacy safeguard.
Use: derive its positive lower bound, upper consistency bound, and strict
acceptance margin from the actual upper Schur endpoint. Source: scalar
interval projection and the existing curvature-clipping theorem.
-/
namespace krylov.XR
noncomputable section

/-- The literal algorithmic floor lies in the original printed interval.
Article: main_krylov, prop:floor. -/
theorem adequacyFloor_mem {sigma eta upperCoefficient directionNormSq : ℝ}
    (ha : 1≤2*(1-sigma)-eta) (hκ : 0≤upperCoefficient) (hd : 0≤directionNormSq)
    (estimate : ℝ) :
    upperCoefficient*directionNormSq/(2*(1-sigma)-eta)≤
      adequacyFloor sigma eta upperCoefficient directionNormSq estimate ∧
    adequacyFloor sigma eta upperCoefficient directionNormSq estimate≤
      upperCoefficient*directionNormSq := by
  have hu : upperCoefficient*directionNormSq/(2*(1-sigma)-eta)≤
      upperCoefficient*directionNormSq :=
    div_le_self (mul_nonneg hκ hd) ha
  exact ⟨le_min (le_max_right _ _) hu,min_le_right _ _⟩

/-- The original spectral lower and upper bounds give precisely the
uniform safeguard constants stated in the article. Article: prop:floor. -/
theorem adequacyFloor_spectral_bounds {sigma eta upperCoefficient directionNormSq mu L : ℝ}
    (ha : 1≤2*(1-sigma)-eta) (hmu : 0<mu)
    (hl : mu/2≤upperCoefficient) (hu : upperCoefficient≤L) (hd : 0≤directionNormSq)
    (estimate : ℝ) :
    (mu/(2*(2*(1-sigma)-eta)))*directionNormSq≤
      adequacyFloor sigma eta upperCoefficient directionNormSq estimate ∧
    adequacyFloor sigma eta upperCoefficient directionNormSq estimate≤L*directionNormSq := by
  have ha' : 0<2*(1-sigma)-eta := by linarith
  have hκ : 0≤upperCoefficient := by linarith
  have hm := adequacyFloor_mem ha hκ hd estimate
  constructor
  · calc
      _ = (mu/2*directionNormSq)/(2*(1-sigma)-eta) := by field_simp
      _ ≤ upperCoefficient*directionNormSq/(2*(1-sigma)-eta) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl hd) ha'.le
      _ ≤ _ := hm.1
  · exact hm.2.trans (mul_le_mul_of_nonneg_right hu hd)

/-- A true upper Schur error bound yields the actual curvature-ratio
margin of the floored trial. No acceptance predicate is assumed.
Article: main_krylov, prop:floor. -/
theorem adequacyFloor_curvature_ratio {sigma eta upperCoefficient directionNormSq curvature ε mu : ℝ}
    (ha : 1≤2*(1-sigma)-eta) (hmu : 0<mu)
    (hl : mu/2≤upperCoefficient) (hd : 0<directionNormSq) (hε : 0≤ε)
    (hcurv : curvature≤(upperCoefficient+ε)*directionNormSq) (estimate : ℝ) :
    curvature/adequacyFloor sigma eta upperCoefficient directionNormSq estimate≤
      2*(1-sigma)-eta+ε/(mu/(2*(2*(1-sigma)-eta))) := by
  let a := 2*(1-sigma)-eta
  let ℓ := mu/(2*a)
  have ha' : 0<a := by dsimp only [a]; linarith
  have hℓ : 0<ℓ := by dsimp only [ℓ]; positivity
  have hκ : 0≤upperCoefficient := by linarith
  have hb := adequacyFloor_mem ha hκ hd.le estimate
  have hs := (adequacyFloor_spectral_bounds ha hmu hl le_rfl hd.le estimate).1
  have hc : 0<adequacyFloor sigma eta upperCoefficient directionNormSq estimate :=
    (mul_pos hℓ hd).trans_le hs
  apply (div_le_iff₀ hc).mpr
  have he : ε*directionNormSq≤(ε/ℓ)*adequacyFloor sigma eta upperCoefficient directionNormSq estimate := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hℓ).mpr
    have hh := mul_le_mul_of_nonneg_left hs hε
    convert hh using 1
    ring
  have hf : upperCoefficient*directionNormSq≤a*
      adequacyFloor sigma eta upperCoefficient directionNormSq estimate :=
    by simpa only [mul_comm] using (div_le_iff₀ ha').mp hb.1
  change curvature≤(a+ε/ℓ)*_
  nlinarith

/-- Small genuine Schur error supplies the stated half-margin in the
Armijo adequacy condition. Article: main_krylov, prop:floor. -/
theorem adequacyFloor_strict_margin {sigma eta upperCoefficient directionNormSq curvature ε mu : ℝ}
    (ha : 1≤2*(1-sigma)-eta) (hmu : 0<mu)
    (hl : mu/2≤upperCoefficient) (hd : 0<directionNormSq) (hε : 0≤ε)
    (hcurv : curvature≤(upperCoefficient+ε)*directionNormSq)
    (hsmall : ε/(mu/(2*(2*(1-sigma)-eta)))≤eta/2) (estimate : ℝ) :
    curvature/adequacyFloor sigma eta upperCoefficient directionNormSq estimate≤
      2*(1-sigma)-eta/2 := by
  have hh := adequacyFloor_curvature_ratio ha hmu hl hd hε hcurv estimate
  linarith

/-- The upper consistency clip alone never worsens the quadratic trial
error. Raising a trial to the adequacy floor is handled independently.
Article: main_krylov, prop:floor and thm:radau. -/
theorem upper_clip_trial_error {upper curvature estimate : ℝ}
    (hc : 0<curvature) (hupper : curvature≤upper) (he : 0<estimate) :
    |1-curvature/min estimate upper|≤|1-curvature/estimate| := by
  have hh := krylov.Completion.clip_curvature_trial_error hc le_rfl hupper he
  have hm : krylov.Completion.clipCurvature curvature upper estimate=
      max curvature (min estimate upper) := by
    rw [krylov.Completion.clipCurvature,min_comm]
  by_cases h : estimate≤upper
  · simp only [min_eq_left h]
    exact le_rfl
  · have hlt : upper<estimate := lt_of_not_ge h
    rw [min_eq_right hlt.le]
    have heq : krylov.Completion.clipCurvature curvature upper estimate=upper := by
      rw [hm,min_eq_right hlt.le,max_eq_right hupper]
    simpa only [heq] using hh

end
end krylov.XR
