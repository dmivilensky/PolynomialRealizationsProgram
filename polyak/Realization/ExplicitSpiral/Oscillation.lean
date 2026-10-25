import polyak.Realization.ExplicitSpiral.NormalForm
import polyak.Realization.ExplicitSpiral.StationaryTable

/-!
Article: the exact initialized spiral oscillation and its three residue phases.
Use: the finite rational signs control every index in the infinite table.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section

/-- Article: every spiral power is its exact radial power times its unit phase. -/
theorem radial_wave_pow {r : ℝ} (hr : 0<r) (k : ℕ) :
    radialWave r^k=((r^k : ℝ) : ℂ)*unitPhase ((k : ℝ)*Real.arccos (radialCosine r)) := by
  rw [radialWave,Waves.z_pow]
  have he : (k : ℂ)*((Real.log r : ℂ)+(Real.arccos (radialCosine r) : ℂ)*Complex.I)=
      ((k : ℝ)*Real.log r : ℝ)+
        (((k : ℝ)*Real.arccos (radialCosine r) : ℝ) : ℂ)*Complex.I := by
    push_cast
    ring
  rw [he,Complex.exp_add,← Complex.ofReal_exp,Real.exp_nat_mul,Real.exp_log hr]
  rfl

/-- Article: Chebyshev coordinates are exactly the unit phase at every positive index. -/
theorem unitPhase_radial_coordinates {r : ℝ} (hr : 0<r) (k : ℕ) (hk : 1≤k) :
    (unitPhase ((k : ℝ)*Real.arccos (radialCosine r))).re=
      Spectral.chebT k (radialCosine r) ∧
    (unitPhase ((k : ℝ)*Real.arccos (radialCosine r))).im=
      (radialWave r).im/r*Spectral.chebU (k-1) (radialCosine r) := by
  have hc := radialCosine_mem hr
  have hc' : -1≤radialCosine r ∧ radialCosine r≤1 :=
    ⟨by linarith [hc.1],by linarith [hc.2]⟩
  constructor
  · rw [unitPhase_re]
    have hh := Spectral.chebT_cos k (Real.arccos (radialCosine r))
    rw [Real.cos_arccos hc'.1 hc'.2] at hh
    exact hh.symm
  · rw [unitPhase_im]
    have hz : (radialWave r).im=r*Real.sin (Real.arccos (radialCosine r)) := by
      simpa only [radialWave,pow_one,Nat.cast_one,one_mul,Real.exp_log hr] using
        Waves.z_pow_im (Real.log r) (Real.arccos (radialCosine r)) 1
    have hu := Spectral.chebU_sin (k-1) (Real.arccos (radialCosine r))
    rw [Real.cos_arccos hc'.1 hc'.2] at hu
    have hnat : ((k-1 : ℕ) : ℝ)+1=k := by exact_mod_cast Nat.sub_add_cancel hk
    rw [hnat] at hu
    rw [← hu,hz]
    field_simp

/-- Article: each finite residue expression is the real part of the genuine complex phase. -/
theorem source_residue_eq {r q : ℝ} (hr : 0<r) (δ : ℝ) (j : ℕ) :
    Source.residue r q δ j=
      (oscillationCoefficient r q (radialWave r) δ*
        unitPhase ((j : ℝ)*Real.arccos (radialCosine r))).re := by
  by_cases hj : j=0
  · subst j
    simp [Source.residue,unitPhase,oscillationCoefficient]
  · obtain ⟨hre,him⟩ := unitPhase_radial_coordinates hr j (by omega)
    obtain ⟨_,hn,hz⟩ := radial_wave_coordinates hr
    have hs := imaginarySquare_eq hn hz
    rw [Source.residue,ite_eq_right hj,Complex.mul_re,hre,him]
    simp only [oscillationCoefficient]
    linear_combination Source.betaImag r q δ*Spectral.chebU (j-1) (radialCosine r)/r*hs

end
end polyak.Realization.ExplicitSpiral
