import jacobi.Reference.InitialEnergy
import jacobi.Reference.EnergyGrowth

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The actual original reference energy is propagated from its genuine
small-scale initial state. Its large-frequency bound keeps exactly
exp(t*abs(Im omega)), with a constant independent of the complex frequency.
The argument works on the whole source half interval and throughout
alpha>-1, including the selected limit-circle endpoint regime.
Use: bounds the original reference amplitude on the large-scale portion of the source half interval.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original reference energy has its full inverse-frequency scale and exact imaginary-frequency exponential after the genuine initial point.
Use: bounds the original reference amplitude on the large-scale portion of the source half interval.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: insert the actual proved initial energy in the genuine energy
propagation inequality. At the exact initial time A/(|omega| *t_0)=4*pi*A.
Discard only nonpositive exponent terms, replace the selected initial
power by its proved inverse-frequency bound, and combine the exact
positive exponential factors. -/
theorem waveEnergy_high_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ omega:ℂ,1≤‖omega‖ →
      ∀ t∈Ioc (0:ℝ) (1/2),initialTime omega≤t →
        waveEnergy a omega t≤C*(‖omega‖^(-gamma a)*Real.exp (t*|omega.im|))^2 := by
  -- All constants and initial values come from the actual source wave and true potential.
  obtain ⟨B,hB,henergy⟩ := wave_initial_energy ha
  obtain ⟨A,hA,hprop⟩ := waveEnergy_propagation ha
  refine ⟨B*Real.exp (4*Real.pi*A),by positivity,fun omega homega t ht hstart => ?_⟩
  have hRp : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  obtain ⟨ht0,_⟩ := initialTime_properties homega
  have h0 := henergy omega homega
  have hp := hprop omega hRp (initialTime omega) ht0 t ht hstart
  have hinit := initialTime_power_bound ha homega
  have hg0 := Real.rpow_pos_of_pos ht0.1 (gamma a)
  have hgR := Real.rpow_pos_of_pos hRp (-gamma a)
  have hsquare := (sq_le_sq₀ hg0.le hgR.le).mpr hinit
  have hpow : ((initialTime omega)^(gamma a))^2=(initialTime omega)^(2*gamma a) := by
    rw [show 2*gamma a=gamma a*2 by ring,Real.rpow_mul ht0.1.le,Real.rpow_two]
  rw [hpow] at hsquare
  have hshift : A/(‖omega‖*initialTime omega)=4*Real.pi*A := by
    dsimp [initialTime]
    field_simp [Real.pi_ne_zero,hRp.ne']
  have hexponent : 2*|omega.im| *(t-initialTime omega)+A/(‖omega‖*initialTime omega)-A/(‖omega‖*t)≤
      2*(t*|omega.im|)+4*Real.pi*A := by
    rw [hshift]
    have hneg : 0≤2*|omega.im| * initialTime omega := mul_nonneg (by positivity) ht0.1.le
    nlinarith [hneg,div_nonneg hA.le (mul_pos hRp ht.1).le]
  have he0 := frequencyEnergy_nonneg omega (wave a omega (initialTime omega)) (waveSlope a omega (initialTime omega))
  have hbound : waveEnergy a omega t≤
      B*(‖omega‖^(-gamma a))^2*Real.exp (2*(t*|omega.im|)+4*Real.pi*A) := by
    calc
      _ ≤ waveEnergy a omega (initialTime omega)*Real.exp
          (2*|omega.im| *(t-initialTime omega)+A/(‖omega‖*initialTime omega)-A/(‖omega‖*t)) := hp
      _ ≤ waveEnergy a omega (initialTime omega)*Real.exp (2*(t*|omega.im|)+4*Real.pi*A) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) he0
      _ ≤ (B*(initialTime omega)^(2*gamma a))*Real.exp (2*(t*|omega.im|)+4*Real.pi*A) :=
        mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare hB.le) (Real.exp_pos _).le
  apply hbound.trans_eq
  have hex : Real.exp (2*(t*|omega.im|))=(Real.exp (t*|omega.im|))^2 := by
    rw [show 2*(t*|omega.im|)=(t*|omega.im|)+(t*|omega.im|) by ring,Real.exp_add,pow_two]
  rw [Real.exp_add,hex,mul_pow]
  ring

/-- The genuine original reference wave has the inverse-frequency amplitude bound with its exact exponential type after the actual initial point.
Use: combines with the proved small-scale branch estimate to control the entire source half interval.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the genuine wave norm square is at most its actual nonnegative
state energy. Apply the proved energy bound and take the positive
square root of its fixed coefficient. -/
theorem wave_high_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ omega:ℂ,1≤‖omega‖ →
      ∀ t∈Ioc (0:ℝ) (1/2),initialTime omega≤t →
        ‖wave a omega t‖≤C*‖omega‖^(-gamma a)*Real.exp (t*|omega.im|) := by
  -- The estimate concerns the true solution value, rather than only an abstract state norm.
  obtain ⟨B,hB,henergy⟩ := waveEnergy_high_bound ha
  refine ⟨Real.sqrt B,Real.sqrt_pos.mpr hB,fun omega homega t ht hstart => ?_⟩
  have hR : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  have hu : ‖wave a omega t‖^2≤waveEnergy a omega t := by
    unfold waveEnergy frequencyEnergy
    exact le_add_of_nonneg_right (by positivity)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤Real.sqrt B*‖omega‖^(-gamma a)*Real.exp (t*|omega.im|))).mp
  have hh := hu.trans (henergy omega homega t ht hstart)
  simpa only [mul_pow,Real.sq_sqrt hB.le,mul_assoc] using hh

/-- The genuine original reference wave has the full half-interval inverse-frequency bound and the exact source imaginary-frequency exponential for every large complex frequency.
Use: supplies actual uniform spectral summand bounds, the reference exponential type and Cauchy estimates for energy perturbations in GL.
Article: jacobi, Lemma C.1.
Proof: after the genuine initial point use the proved actual energy
bound. Before it use the proved selected-branch estimate and monotonicity
of the positive endpoint power. At zero the actual original prefactor
vanishes. One fixed positive constant covers both physical regions. -/
theorem wave_uniform_high_frequency {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ omega:ℂ,1≤‖omega‖ → ∀ t∈Icc (0:ℝ) (1/2),
      ‖wave a omega t‖≤C*‖omega‖^(-gamma a)*Real.exp (t*|omega.im|) := by
  -- Both bounds apply to the same actual source solution and its selected endpoint branch.
  obtain ⟨A,D,hA,_,hsmall⟩ := wave_small_scale ha
  obtain ⟨B,hB,hlarge⟩ := wave_high_bound ha
  refine ⟨A+B,by positivity,fun omega homega t ht => ?_⟩
  have hR : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  have hpow := Real.rpow_pos_of_pos hR (-gamma a)
  have hexp := Real.exp_pos (t*|omega.im|)
  by_cases ht0 : t=0
  · subst t
    simp only [wave,(weight_properties ha).2.1,Complex.ofReal_zero,zero_mul,norm_zero]
    positivity
  have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  by_cases hstart : initialTime omega≤t
  · exact (hlarge omega homega t ⟨htp,ht.2⟩ hstart).trans
      (by gcongr; linarith)
  · have hinit := initialTime_properties homega
    have hscaled := mul_le_mul_of_nonneg_left (le_of_not_ge hstart)
      (show 0≤Real.pi*‖omega‖ by positivity)
    have hss : Real.pi*‖omega‖*t≤1/4 := by nlinarith [hinit.2]
    have hu := (hsmall omega homega t ⟨htp,ht.2⟩ hss).1
    have hp := (Real.rpow_le_rpow htp.le (le_of_not_ge hstart)
      (by linarith [(parameters ha).1] : 0≤gamma a)).trans (initialTime_power_bound ha homega)
    have he : 1≤Real.exp (t*|omega.im|) := Real.one_le_exp (by positivity)
    calc
      _ ≤ A*t^(gamma a) := hu
      _ ≤ A*‖omega‖^(-gamma a) := mul_le_mul_of_nonneg_left hp hA.le
      _ ≤ (A+B)*‖omega‖^(-gamma a) := by gcongr; linarith
      _ ≤ (A+B)*‖omega‖^(-gamma a)*Real.exp (t*|omega.im|) :=
        le_mul_of_one_le_right (by positivity) he

end
end jacobi.Reference
