import jacobi.Reference.HighFrequency
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
The actual spatial derivative has its sharp high-frequency bound
O(|omega|^(1-gamma)*exp(t*|Im omega|)) away from the selected
singular endpoint. This follows directly from the already proved
genuine state-energy estimate and does not require a new ODE comparison.
Use: waveSlope_away_bound and the true spectral Cauchy estimate provide the spatial derivatives needed for the sharpened GL series.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The actual reference slope has the genuine sharp high-frequency size after its original initial point.
Use: waveSlope_away_bound and the true spectral Cauchy estimate provide the spatial derivatives needed for the sharpened GL series.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the original slope divided by frequency is a component of
the proved nonnegative reference state energy. Take its genuine
square-root bound and combine exactly the positive frequency powers. -/
theorem waveSlope_high_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ omega:ℂ,1≤‖omega‖ →
      ∀ t∈Ioc (0:ℝ) (1/2),initialTime omega≤t →
        ‖waveSlope a omega t‖≤C*‖omega‖^(1-gamma a)*Real.exp (t*|omega.im|) := by
  -- The energy contains the actual derivative; no derivative of a bound is taken.
  obtain ⟨B,hB,henergy⟩ := waveEnergy_high_bound ha
  refine ⟨Real.sqrt B,Real.sqrt_pos.mpr hB,fun omega homega t ht hstart => ?_⟩
  have hR : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  have hv : (‖waveSlope a omega t‖/‖omega‖)^2≤waveEnergy a omega t := by
    unfold waveEnergy frequencyEnergy
    rw [div_pow]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hsq := hv.trans (henergy omega homega t ht hstart)
  have hh : ‖waveSlope a omega t‖/‖omega‖≤
      Real.sqrt B*‖omega‖^(-gamma a)*Real.exp (t*|omega.im|) := by
    apply (sq_le_sq₀ (by positivity : 0≤‖waveSlope a omega t‖/‖omega‖)
      (by positivity : 0≤Real.sqrt B*‖omega‖^(-gamma a)*Real.exp (t*|omega.im|))).mp
    simpa only [mul_pow,Real.sq_sqrt hB.le,mul_assoc] using hsq
  have hpow : ‖omega‖^(-gamma a)*‖omega‖=‖omega‖^(1-gamma a) := by
    calc
      _ = ‖omega‖^(-gamma a)*‖omega‖^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring
  have hmul := (div_le_iff₀ hR).mp hh
  exact hmul.trans_eq (by rw [show Real.sqrt B*‖omega‖^(-gamma a)*Real.exp (t*|omega.im|)*‖omega‖=
    Real.sqrt B*(‖omega‖^(-gamma a)*‖omega‖)*Real.exp (t*|omega.im|) by ring,hpow])

/-- At high frequency the genuine initial point lies before every fixed physical cutoff delta.
Use: waveSlope_away_bound puts the actual energy bound on the whole original differentiability strip without a hidden initial-state premise.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the original initial point is 1/(4*pi*|omega|)<=1/|omega|;
the assumed genuine frequency threshold implies 1/|omega|<=delta. -/
theorem initialTime_le_cutoff {d : ℝ} (hd : 0<d) {omega : ℂ}
    (hR : 1≤‖omega‖) (hdR : 1/d≤‖omega‖) : initialTime omega≤d := by
  -- Both reciprocal denominators are genuinely positive at the original frequency threshold.
  have hp : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one hR
  have hcut : 1/‖omega‖≤d := (div_le_iff₀ hp).mpr (by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp hdR)
  have hfirst : initialTime omega≤1/‖omega‖ := by
    unfold initialTime
    apply one_div_le_one_div_of_le hp
    nlinarith [Real.pi_gt_three]
  exact hfirst.trans hcut

/-- The actual spatial slope has the sharp original frequency bound uniformly on every fixed half-interval strip away from zero.
Use: slope energy-derivative estimates control the actual spatial derivatives of the difference between the two spectral reference functions in F.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the proved explicit frequency threshold places the actual
initial point before delta. Apply the genuine original slope energy
bound at every original t in the whole physical strip. -/
theorem waveSlope_away_bound {a : ℝ} (ha : -1<a) {d : ℝ} (hd : 0<d) :
    ∃ C : ℝ,0<C ∧ ∀ omega:ℂ,max 1 (1/d)≤‖omega‖ →
      ∀ t∈Icc d (1/2),
        ‖waveSlope a omega t‖≤C*‖omega‖^(1-gamma a)*Real.exp (t*|omega.im|) := by
  obtain ⟨C,hC,hbound⟩ := waveSlope_high_bound ha
  refine ⟨C,hC,fun omega hR t ht => ?_⟩
  have hR1 := (le_max_left 1 (1/d)).trans hR
  exact hbound omega hR1 t ⟨hd.trans_le ht.1,ht.2⟩
    ((initialTime_le_cutoff hd hR1 ((le_max_right 1 (1/d)).trans hR)).trans ht.1)

end
end jacobi.Reference
