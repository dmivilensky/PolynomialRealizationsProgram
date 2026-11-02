import jacobi.Analytic.ReferencePropagation
import jacobi.Analytic.ReferenceInitialState

/-!
Article: jacobi, Lemma C.1.
The actual uniform initial energy and the genuine complex-order
propagation estimate give the inverse-frequency wave bound on the
whole original half interval, with its exact imaginary-frequency type.
Use: starts the complex-order frequency propagation from the original selected solution, without assuming an asymptotic initial state.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual reference energy at its genuine initial time has a common endpoint-power bound for every order in the complex parameter set.
Use: starts the complex-order frequency propagation from the original selected solution, without assuming an asymptotic initial state.
Article: jacobi, Lemma C.1.
Proof: evaluate the two actual initial-scale state bounds at
1/(4*pi*|omega|). The slope divided by frequency has the same endpoint
power as the wave; square both estimates and add them. -/
theorem wave_initial_energy {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ a omega : ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → 1≤‖omega‖ →
        waveEnergy a omega (initialTime omega)≤C*(initialTime omega)^(2*(gamma a).re) := by
  -- The starting state is the actual source solution, with no independent asymptotic normalization premise.
  obtain ⟨A,B,hA,hB,hsmall⟩ := wave_small_scale hG hδ
  refine ⟨A^2+(4*Real.pi*B)^2,by positivity,fun a omega hag ha hc homega => ?_⟩
  obtain ⟨ht,hscale⟩ := initialTime_properties homega
  have hRp : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  have hg : 0<(initialTime omega)^((gamma a).re) := Real.rpow_pos_of_pos ht.1 _
  obtain ⟨hu,hv⟩ := hsmall a omega hag ha hc homega (initialTime omega) ht hscale.le
  have hv' : ‖waveSlope a omega (initialTime omega)‖/‖omega‖≤
      (4*Real.pi*B)*(initialTime omega)^((gamma a).re) := by
    apply (div_le_iff₀ hRp).mpr
    apply hv.trans_eq
    dsimp [initialTime]
    field_simp [Real.pi_ne_zero,hRp.ne']
  have hu2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤A*(initialTime omega)^((gamma a).re))).mpr hu
  have hv2 := (sq_le_sq₀ (by positivity : 0≤‖waveSlope a omega (initialTime omega)‖/‖omega‖)
    (by positivity : 0≤(4*Real.pi*B)*(initialTime omega)^((gamma a).re))).mpr hv'
  have hpower : ((initialTime omega)^((gamma a).re))^2=(initialTime omega)^(2*(gamma a).re) := by
    rw [show 2*(gamma a).re=(gamma a).re*2 by ring,Real.rpow_mul ht.1.le,Real.rpow_two]
  unfold waveEnergy frequencyEnergy
  rw [div_pow] at hv2
  rw [mul_pow,hpower] at hu2 hv2
  nlinarith

/-- The actual original reference energy has its full inverse-frequency scale and exact imaginary-frequency exponential after the genuine initial point.
Use: bounds the original reference amplitude on the large-scale portion of the source half interval.
Article: jacobi, Lemma C.1.
Proof: insert the actual proved initial energy in the genuine energy
propagation inequality. At the exact initial time A/(|omega| *t_0)=4*pi*A.
Discard only nonpositive exponent terms, replace the selected initial
power by its proved inverse-frequency bound, and combine the exact
positive exponential factors. -/
theorem waveEnergy_high_bound {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ a omega : ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → 1≤‖omega‖ →
      ∀ t∈Ioc (0:ℝ) (1/2),initialTime omega≤t →
        waveEnergy a omega t≤C*(‖omega‖^(-(gamma a).re)*Real.exp (t*|omega.im|))^2 := by
  -- All constants and initial values come from the actual source wave and true potential.
  obtain ⟨B,hB,henergy⟩ := wave_initial_energy hG hδ
  obtain ⟨A,hA,hprop⟩ := waveEnergy_propagation hG
  refine ⟨B*Real.exp (4*Real.pi*A),by positivity,fun a omega hag ha hc homega t ht hstart => ?_⟩
  have hRp : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  obtain ⟨ht0,_⟩ := initialTime_properties homega
  have h0 := henergy a omega hag ha hc homega
  have hp := hprop a hag ha omega hRp (initialTime omega) ht0 t ht hstart
  have hinit := initialTime_power_bound hag homega
  have hg0 := Real.rpow_pos_of_pos ht0.1 ((gamma a).re)
  have hgR := Real.rpow_pos_of_pos hRp (-(gamma a).re)
  have hsquare := (sq_le_sq₀ hg0.le hgR.le).mpr hinit
  have hpow : ((initialTime omega)^((gamma a).re))^2=(initialTime omega)^(2*(gamma a).re) := by
    rw [show 2*(gamma a).re=(gamma a).re*2 by ring,Real.rpow_mul ht0.1.le,Real.rpow_two]
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
      B*(‖omega‖^(-(gamma a).re))^2*Real.exp (2*(t*|omega.im|)+4*Real.pi*A) := by
    calc
      _ ≤ waveEnergy a omega (initialTime omega)*Real.exp
          (2*|omega.im| *(t-initialTime omega)+A/(‖omega‖*initialTime omega)-A/(‖omega‖*t)) := hp
      _ ≤ waveEnergy a omega (initialTime omega)*Real.exp (2*(t*|omega.im|)+4*Real.pi*A) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) he0
      _ ≤ (B*(initialTime omega)^(2*(gamma a).re))*Real.exp (2*(t*|omega.im|)+4*Real.pi*A) :=
        mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare hB.le) (Real.exp_pos _).le
  apply hbound.trans_eq
  have hex : Real.exp (2*(t*|omega.im|))=(Real.exp (t*|omega.im|))^2 := by
    rw [show 2*(t*|omega.im|)=(t*|omega.im|)+(t*|omega.im|) by ring,Real.exp_add,pow_two]
  rw [Real.exp_add,hex,mul_pow]
  ring

/-- The genuine original reference wave has the inverse-frequency amplitude bound with its exact exponential type after the actual initial point.
Use: combines with the proved small-scale branch estimate to control the entire source half interval.
Article: jacobi, Lemma C.1.
Proof: the genuine wave norm square is at most its actual nonnegative
state energy. Apply the proved energy bound and take the positive
square root of its fixed coefficient. -/
theorem wave_high_bound {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ a omega : ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → 1≤‖omega‖ →
      ∀ t∈Ioc (0:ℝ) (1/2),initialTime omega≤t →
        ‖wave a omega t‖≤C*‖omega‖^(-(gamma a).re)*Real.exp (t*|omega.im|) := by
  -- The estimate concerns the true solution value, rather than only an abstract state norm.
  obtain ⟨B,hB,henergy⟩ := waveEnergy_high_bound hG hδ
  refine ⟨Real.sqrt B,Real.sqrt_pos.mpr hB,fun a omega hag ha hc homega t ht hstart => ?_⟩
  have hR : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  have hu : ‖wave a omega t‖^2≤waveEnergy a omega t := by
    unfold waveEnergy frequencyEnergy
    exact le_add_of_nonneg_right (by positivity)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤Real.sqrt B*‖omega‖^(-(gamma a).re)*Real.exp (t*|omega.im|))).mp
  have hh := hu.trans (henergy a omega hag ha hc homega t ht hstart)
  simpa only [mul_pow,Real.sq_sqrt hB.le,mul_assoc] using hh

/-- The genuine original reference wave has the full half-interval inverse-frequency bound and the exact source imaginary-frequency exponential for every large complex frequency.
Use: supplies actual uniform spectral summand bounds, the reference exponential type and Cauchy estimates for energy perturbations in GL.
Article: jacobi, Lemma C.1.
Proof: after the genuine initial point use the proved actual energy
bound. Before it use the proved selected-branch estimate and monotonicity
of the positive endpoint power. At zero the actual original prefactor
vanishes. One fixed positive constant covers both physical regions. -/
theorem wave_uniform_high_frequency {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ a omega : ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → 1≤‖omega‖ → ∀ t∈Icc (0:ℝ) (1/2),
      ‖wave a omega t‖≤C*‖omega‖^(-(gamma a).re)*Real.exp (t*|omega.im|) := by
  -- Both bounds apply to the same actual source solution and its selected endpoint branch.
  obtain ⟨A,D,hA,_,hsmall⟩ := wave_small_scale hG hδ
  obtain ⟨B,hB,hlarge⟩ := wave_high_bound hG hδ
  refine ⟨A+B,by positivity,fun a omega hag ha hc homega t ht => ?_⟩
  have hR : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  have hpow := Real.rpow_pos_of_pos hR (-(gamma a).re)
  have hexp := Real.exp_pos (t*|omega.im|)
  by_cases ht0 : t=0
  · subst t
    have hg : gamma a≠0 := ne_of_apply_ne Complex.re hag.ne'
    simp only [wave,weight,mul_zero,Real.sin_zero,zero_div,Complex.ofReal_zero,Complex.zero_cpow hg,zero_mul,norm_zero]
    positivity
  have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  by_cases hstart : initialTime omega≤t
  · exact (hlarge a omega hag ha hc homega t ⟨htp,ht.2⟩ hstart).trans
      (by gcongr; linarith)
  · have hinit := initialTime_properties homega
    have hscaled := mul_le_mul_of_nonneg_left (le_of_not_ge hstart)
      (show 0≤Real.pi*‖omega‖ by positivity)
    have hss : Real.pi*‖omega‖*t≤1/4 := by nlinarith [hinit.2]
    have hu := (hsmall a omega hag ha hc homega t ⟨htp,ht.2⟩ hss).1
    have hp := (Real.rpow_le_rpow htp.le (le_of_not_ge hstart)
      hag.le).trans (initialTime_power_bound hag homega)
    have he : 1≤Real.exp (t*|omega.im|) := Real.one_le_exp (by positivity)
    calc
      _ ≤ A*t^((gamma a).re) := hu
      _ ≤ A*‖omega‖^(-(gamma a).re) := mul_le_mul_of_nonneg_left hp hA.le
      _ ≤ (A+B)*‖omega‖^(-(gamma a).re) := by gcongr; linarith
      _ ≤ (A+B)*‖omega‖^(-(gamma a).re)*Real.exp (t*|omega.im|) :=
        le_mul_of_one_le_right (by positivity) he

end
end jacobi.ComplexReference
