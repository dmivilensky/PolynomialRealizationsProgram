import jacobi.Elliptic.StrictImprovement
import jacobi.Bessel.EdgeData
import jacobi.Analytic.YoungLower
import jacobi.Reference.Parameters
import jacobi.Variational.LowerConstant

/-!
Article: jacobi, Proposition C.4.
The original Bessel moments determine the transition exactly at alpha=1/2.
Every actual minimizer in the Young regime has the source's precise
sech-fourth amplitude and arbitrary translation; below that threshold
the actual attained calibration is strictly larger than the Young value.
This reuses the complete equality classification and direct method.
Use: bessel_young_minimizer and bessel_second_strict_young apply the existing general calibration without new variational assumptions.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set MeasureTheory jacobi.Variational jacobi.Young
open scoped ENNReal

/-- The original Bessel second-moment Young regime starts exactly at the source order U.
Use: bessel_young_minimizer and bessel_second_strict_young apply the existing general calibration without new variational assumptions.
Article: jacobi, Proposition C.4.
Proof: the actual ratio T_2/M^2 is 1/(alpha+2); its denominator and M^2 are strictly positive. -/
theorem bessel_young_regime {a:ℝ} (ha:-1<a) :
    5*(jacobi.Bessel.edgeSpectrum a ha).second≤2*(jacobi.Bessel.edgeSpectrum a ha).mass^2 ↔ 1/2≤a := by
  -- The ratio identity is for the actual spectrum; both cleared denominators are strictly positive.
  have hM := (jacobi.Bessel.edgeSpectrum a ha).mass_pos
  have hden : 0<a+2 := by linarith
  have hshape := jacobi.Bessel.edgeSpectrum_shape ha
  have hid : (jacobi.Bessel.edgeSpectrum a ha).second=
      (jacobi.Bessel.edgeSpectrum a ha).mass^2/(a+2) := by
    apply (eq_div_iff hden.ne').mpr
    field_simp [(sq_pos_of_pos hM).ne',hden.ne'] at hshape
    nlinarith [hshape]
  rw [hid]
  constructor
  · intro h
    have hh := (div_le_iff₀ hden).mp (show
      (5*(jacobi.Bessel.edgeSpectrum a ha).mass^2)/(a+2)≤2*(jacobi.Bessel.edgeSpectrum a ha).mass^2 by
        simpa only [mul_div_assoc] using h)
    nlinarith [sq_pos_of_pos hM]
  · intro h
    rw [← mul_div_assoc,div_le_iff₀ hden]
    nlinarith [sq_pos_of_pos hM]

/-- Every genuine minimizer in the Young regime has exactly the source's amplitude, up to translation and null sets.
Use: bessel_young_minimizer proves the all-minimizer assertion in Proposition C.4, rather than only exhibiting a candidate.
Article: jacobi, Proposition C.4.
Proof: the actual infimum equals the Young bound. Its attaining density
therefore has active second moment and satisfies equality in sharp Young.
The proved full equality classification gives b*sech^4; its actual second
moment 32*b^2/45 fixes the positive amplitude uniquely. -/
theorem young_minimizer {M T:ℝ} (hM:0≤M) (hT:0<T) (hr:5*T≤2*M^2)
    (m:Density) (hmT:T≤observe m .second)
    (hmin:m.cost=relaxedInfimum {Observation.second} M (fun _ => T)) :
    ∃x₀:ℝ,m.value=ᵐ[volume] (fun x => sqrt (45*T/32)*sech (x-x₀)^4) := by
  -- The source's arbitrary measurable minimizer is retained throughout the equality argument.
  have hm : 0<m.mass := mass_pos_of_observe_pos m .second (hT.trans_le hmT)
  have he : m.energy=youngValue T := by
    rw [second_calibration_young hM hT.le hr] at hmin
    have h := congrArg ENNReal.toReal hmin
    simpa only [m.cost_toReal,ENNReal.toReal_ofReal (youngValue_nonneg hT.le)] using h
  obtain ⟨hG,hY⟩ := jacobi.Elliptic.energy_at_young_value hT m hmT he
  obtain ⟨b,x₀,hb,hae⟩ := young_equality_necessary m hm hY
  have hmq : m.value=ᵐ[volume] ((equalityFamily b hb.le).translate x₀).value := hae
  have hq := observe_congr hmq .second
  rw [Density.translate_second,equalityFamily_second,hG] at hq
  have hb2 : b^2=45*T/32 := by linarith
  have hbval : sqrt (45*T/32)=b := by rw [← hb2,Real.sqrt_sq hb.le]
  exact ⟨x₀,by simpa only [hbval] using hae⟩

/-- Every actual Bessel Young-regime minimizer is precisely a translate of the source's sech-fourth profile.
Use: the remaining tail comparison of Proposition C.4 compares its forced exponent with the persymmetric packing density.
Article: jacobi, Proposition C.4.
Proof: apply the general all-minimizer classification to the genuine
Bessel mass and second moment, with their proved exact regime condition. -/
theorem bessel_young_minimizer {a:ℝ} (ha:-1<a) (hU:1/2≤a) (m:Density)
    (hmT:(jacobi.Bessel.edgeSpectrum a ha).second≤observe m .second)
    (hmin:m.cost=relaxedInfimum {Observation.second} (jacobi.Bessel.edgeSpectrum a ha).mass
      (fun _ => (jacobi.Bessel.edgeSpectrum a ha).second)) :
    ∃x₀:ℝ,m.value=ᵐ[volume] (fun x =>
      sqrt (45*(jacobi.Bessel.edgeSpectrum a ha).second/32)*sech (x-x₀)^4) :=
  young_minimizer (jacobi.Bessel.edgeSpectrum a ha).mass_pos.le
    (jacobi.Variational.EdgeSpectrum.second_pos _) ((bessel_young_regime ha).mpr hU) m hmT hmin

/-- Below U the genuine attained Bessel level-two calibration is strictly above the actual printed Young value.
Use: closes the strict-calibration assertion of Proposition C.4 using the existing direct method and equality necessity.
Article: jacobi, Proposition C.4.
Proof: the actual Bessel spectrum is strictly subcritical, and its shape
ratio is in the elliptic regime exactly below U. The already proved strict
Young improvement applies to those same mass and moment thresholds. -/
theorem bessel_second_strict_young {a:ℝ} (ha:-1<a) (hU:a<1/2) :
    ENNReal.ofReal (jacobi.Parameter.youngLower a)<
      relaxedInfimum {Observation.second} (jacobi.Bessel.edgeSpectrum a ha).mass
        (fun _ => (jacobi.Bessel.edgeSpectrum a ha).second) := by
  rw [jacobi.Parameter.youngLower_spectral ha]
  apply jacobi.Elliptic.second_infimum_strict_young (jacobi.Bessel.edgeSpectrum a ha).mass_pos
    (jacobi.Variational.EdgeSpectrum.second_pos _) (jacobi.Bessel.edgeSpectrum a ha).second_lt_mass_sq
  exact lt_of_not_ge (fun h => (not_le_of_gt hU) ((bessel_young_regime ha).mp h))

/-- The actual explicit Young extremal violates the Bessel mass constraint strictly below U.
Use: the strictness and optimizer comparison in Proposition C.4 concern the source's same prescribed amplitude, not an arbitrarily rescaled density.
Article: jacobi, Proposition C.4.
Proof: the actual candidate mass is 4a_alpha/3. Its square is 5T_2/2,
which is strictly larger than M^2 below the proved exact regime threshold. -/
theorem bessel_young_mass_gt {a:ℝ} (ha:-1<a) (hU:a<1/2) :
    (jacobi.Bessel.edgeSpectrum a ha).mass<
      (equalityFamily (sqrt (45*(jacobi.Bessel.edgeSpectrum a ha).second/32))
        (sqrt_nonneg _)).mass := by
  -- The prescribed amplitude has squared mass 5*T_2/2; below U this exceeds the actual mass cap squared.
  have hM := (jacobi.Bessel.edgeSpectrum a ha).mass_pos
  have hT := (jacobi.Bessel.edgeSpectrum a ha).second_pos
  have hr : 2*(jacobi.Bessel.edgeSpectrum a ha).mass^2<5*(jacobi.Bessel.edgeSpectrum a ha).second :=
    lt_of_not_ge (fun h => (not_le_of_gt hU) ((bessel_young_regime ha).mp h))
  rw [equalityFamily_mass]
  have hs := Real.sq_sqrt (show 0≤45*(jacobi.Bessel.edgeSpectrum a ha).second/32 by positivity)
  by_contra! hn
  have hsq := (sq_le_sq₀ (show 0≤4*sqrt (45*(jacobi.Bessel.edgeSpectrum a ha).second/32)/3 by positivity) hM.le).mpr hn
  nlinarith [hsq]

/-- The printed positive-regime packing tail exponent equals the Young exponent exactly at U.
Use: the endpoint asymptotics in Proposition C.4 yield the uniqueness comparison in Proposition C.4.
Article: jacobi, Proposition C.4.
Proof: nu=alpha/2+1/4 is positive on the stipulated regime, so the exact scalar division can be cancelled. -/
theorem tail_exponent_eq_four {a:ℝ} (ha:-(1/2:ℝ)<a) :
    2/(jacobi.Reference.gamma a-1/2)=4 ↔ a=1/2 := by
  have hnu : 0< jacobi.Reference.gamma a-1/2 := by dsimp only [jacobi.Reference.gamma]; linarith
  rw [div_eq_iff hnu.ne']
  dsimp only [jacobi.Reference.gamma]
  constructor <;> intro h <;> linarith

end
end jacobi.Trichotomy
