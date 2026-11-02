import jacobi.Support.TransitionState
import jacobi.Support.FrequencyPowers

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The actual support polynomials satisfy the full printed complex
frequency envelope, with its exact minimum, on the full original
growing half chain and imaginary strip. Every transition and
propagation input refers to the same original spectral polynomial.
Use: the original support interpolation estimates, weight asymptotics and two-edge Gram limit use this full uniform envelope at growing as well as fixed spectral indices.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference jacobi.Finite
open scoped Topology

/-- The genuine original support polynomials satisfy the complete source complex frequency envelope.
Use: the original support interpolation estimates, weight asymptotics and two-edge Gram limit use this full uniform envelope at growing as well as fixed spectral indices.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: bounded scaled frequency is controlled by the proved original transition estimates. Otherwise the true sine gap is comparable to the frequency. Start the actual free-state propagation at floor(1/|theta|), use its proved original transition bound, and recover the same original wave. The exact floor inequalities control both the perturbation exponent and the original growth powers, giving the printed minimum. -/
theorem naturalWave_frequency_envelope {a b bnd:ℝ} (ha:-1<a) (hb:-1<b) (hbnd:0<bnd) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+3→∀theta:ℂ,theta≠0→
      |theta.re|≤4*π/5→|theta.im|≤bnd/ jacobi.Jacobi.frequency a b (n+1)→
      ‖naturalWave a b ha hb n m (Complex.cos theta)‖≤
        C*min (((m:ℝ)+1)^gamma a) (‖theta‖^(-gamma a)) := by
  -- The complete original envelope is obtained from proved actual transition and propagation bounds, without a separately assumed spectral-wave estimate.
  let R := 2*bnd+(4*π/5+bnd)+1
  have hR : 0<R := by dsimp [R]; positivity
  obtain ⟨A,hA,htransition⟩ := naturalWave_transition ha hb hR.le
  obtain ⟨S,hS,hstart⟩ := naturalState_transition ha hb hR.le
  obtain ⟨P,hP,hprop⟩ := naturalWave_state_propagation (bnd:=bnd) ha hb
  obtain ⟨c,hc,hsine⟩ := oscillatory_sine_lower
  let Q := exp bnd*S*exp (bnd+P)/c
  have hQ : 0<Q := by dsimp [Q]; positivity
  let C := A+A*R^gamma a+Q*R^gamma a
  have hC : 0<C := by dsimp [C]; positivity
  have hpow0 : 0≤R^gamma a := rpow_nonneg hR.le _
  have hCA : A≤C ∧ A*R^gamma a≤C ∧ Q*R^gamma a≤C := by
    dsimp [C]
    constructor
    · linarith only [mul_nonneg hA.le hpow0,mul_nonneg hQ.le hpow0]
    · constructor <;> linarith only [hA,mul_nonneg hA.le hpow0,mul_nonneg hQ.le hpow0]
  refine ⟨C,hC,?_⟩
  filter_upwards [htransition,hstart,hprop,eventually_ge_atTop (8:ℕ)] with n hnA hnS hnP hlarge
  intro m hm theta htheta hre him
  let t := ‖theta‖
  let x : ℝ := (m:ℝ)+1
  have ht : 0<t := norm_pos_iff.mpr htheta
  have hx : 0<x := by dsimp [x]; positivity
  have hxN : x≤n := by dsimp [x]; exact_mod_cast (show m+1≤n by omega)
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hN := natural_frequency_ge a b ha hb n
  have hN0 := jacobi.Jacobi.frequency_pos ha hb (show 0<n+1 by omega)
  have himN : |theta.im| *(n:ℝ)≤bnd :=
    (mul_le_mul_of_nonneg_left hN (abs_nonneg _)).trans ((le_div_iff₀ hN0).mp him)
  have himb : |theta.im|≤bnd := by
    have h : |theta.im|≤|theta.im| *(n:ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hn1 (abs_nonneg theta.im)
    exact h.trans himN
  have htcap : t≤4*π/5+bnd := (Complex.norm_le_abs_re_add_abs_im theta).trans (add_le_add hre himb)
  have hg : 0≤gamma a := (parameter_pos ha hb).1.le
  have hsmall (hscale:t*x≤R) :
      ‖naturalWave a b ha hb n m (Complex.cos theta)‖≤C*x^gamma a ∧
      ‖naturalWave a b ha hb n m (Complex.cos theta)‖≤C*t^(-gamma a) := by
    have hv := (hnA m hm theta hscale).1
    refine ⟨hv.trans (mul_le_mul_of_nonneg_right hCA.1 (rpow_pos_of_pos hx _).le),?_⟩
    calc
      _ ≤ A*x^gamma a := hv
      _ ≤ A*(R^gamma a*t^(-gamma a)) := mul_le_mul_of_nonneg_left (frequency_power_bound ht hx.le hg hscale) hA.le
      _ = (A*R^gamma a)*t^(-gamma a) := by ring
      _ ≤ C*t^(-gamma a) := mul_le_mul_of_nonneg_right hCA.2.1 (rpow_pos_of_pos ht _).le
  have hboth : ‖naturalWave a b ha hb n m (Complex.cos theta)‖≤C*x^gamma a ∧
      ‖naturalWave a b ha hb n m (Complex.cos theta)‖≤C*t^(-gamma a) := by
    by_cases hhigh:2*bnd<t*(n:ℝ)
    · have hsector : |theta.im|≤t/2 := by
        apply (mul_le_mul_iff_of_pos_right hn0).mp
        nlinarith only [himN,hhigh]
      let L := Nat.floor (1/t)
      let z : ℝ := (L:ℝ)+1
      have hz : 0<z := by dsimp [z]; positivity
      have hfloor : 1≤t*z ∧ t*z≤R := by
        have h := frequency_floor_bounds ht
        exact ⟨h.1,h.2.trans (by dsimp [R]; linarith only [htcap,hbnd])⟩
      by_cases hmL:m≤L
      · apply hsmall
        exact (mul_le_mul_of_nonneg_left (by dsimp [x,z]; exact_mod_cast Nat.add_le_add_right hmL 1) ht.le).trans hfloor.2
      · have hLm : L≤m := by omega
        have hstart' := hnS L (by omega) theta hfloor.2
        have hprop' := hnP theta htheta hre himb hsector L m hLm hm
        have himm : |theta.im| *((m-L:ℕ):ℝ)≤bnd := by
          have hindex : ((m-L:ℕ):ℝ)≤n := by exact_mod_cast (show m-L≤n by omega)
          exact (mul_le_mul_of_nonneg_left hindex (abs_nonneg _)).trans himN
        have hexp : |theta.im| *((m-L:ℕ):ℝ)+P/(t*z)≤bnd+P :=
          add_le_add himm (div_le_self hP.le hfloor.1)
        have hstate : naturalState a b ha hb n m theta≤S*z^(gamma a-1)*exp (bnd+P) := by
          exact hprop'.trans (mul_le_mul hstart' (exp_le_exp.mpr hexp) (exp_pos _).le (by positivity))
        let q := Complex.exp (theta*Complex.I)
        have hgaplo : 2*c*t≤‖q-q⁻¹‖ := by
          dsimp only [q]
          rw [free_frequency_gap]
          linarith only [hsine theta hre hsector]
        have hgap : 0<‖q-q⁻¹‖ := (by positivity : 0<2*c*t).trans_le hgaplo
        have hqn := free_frequency_norms theta
        have hstrip : exp (|theta.im|)≤exp bnd := exp_le_exp.mpr himb
        have hrecovery := free_state_recovery (x:=naturalWave a b ha hb n m (Complex.cos theta))
          (y:=naturalWave a b ha hb n (m+1) (Complex.cos theta)) (Complex.exp_ne_zero _) hgap
          (by simpa only [exp_zero] using exp_le_exp.mpr hbnd.le) (hqn.2.1.trans hstrip) (hqn.2.2.trans hstrip)
        have hratio : 2*exp bnd/‖q-q⁻¹‖≤exp bnd/(c*t) := by
          calc
            _ ≤ 2*exp bnd/(2*c*t) := div_le_div₀ (by positivity) le_rfl (by positivity) hgaplo
            _ = _ := by ring
        have hvalue : ‖naturalWave a b ha hb n m (Complex.cos theta)‖≤Q*z^gamma a := by
          calc
            _ ≤ ‖naturalWave a b ha hb n m (Complex.cos theta)‖+
                ‖naturalWave a b ha hb n (m+1) (Complex.cos theta)‖ := le_add_of_nonneg_right (norm_nonneg _)
            _ ≤ (2*exp bnd/‖q-q⁻¹‖)*naturalState a b ha hb n m theta := hrecovery
            _ ≤ (exp bnd/(c*t))*(S*z^(gamma a-1)*exp (bnd+P)) :=
              mul_le_mul hratio hstate (by dsimp [naturalState,freeState]; positivity) (by positivity)
            _ = Q*(z^gamma a/(t*z)) := by dsimp [Q]; rw [rpow_sub_one hz.ne']; ring
            _ ≤ Q*z^gamma a := mul_le_mul_of_nonneg_left (div_le_self (rpow_pos_of_pos hz _).le hfloor.1) hQ.le
        have hfreq : ‖naturalWave a b ha hb n m (Complex.cos theta)‖≤C*t^(-gamma a) := by
          calc
            _ ≤ Q*z^gamma a := hvalue
            _ ≤ Q*(R^gamma a*t^(-gamma a)) := mul_le_mul_of_nonneg_left (frequency_power_bound ht hz.le hg hfloor.2) hQ.le
            _ = (Q*R^gamma a)*t^(-gamma a) := by ring
            _ ≤ C*t^(-gamma a) := mul_le_mul_of_nonneg_right hCA.2.2 (rpow_pos_of_pos ht _).le
        have hxlarge : 1≤t*x := hfloor.1.trans (mul_le_mul_of_nonneg_left
          (by dsimp [x,z]; exact_mod_cast Nat.add_le_add_right hLm 1) ht.le)
        exact ⟨hfreq.trans (mul_le_mul_of_nonneg_left (inverse_frequency_power_le ht hg hxlarge) hC.le),hfreq⟩
    · apply hsmall
      have hlo : t*(n:ℝ)≤2*bnd := le_of_not_gt hhigh
      exact (mul_le_mul_of_nonneg_left hxN ht.le).trans (hlo.trans (by dsimp [R]; linarith only [hbnd,pi_pos]))
  rw [mul_min_of_nonneg _ _ hC.le]
  exact le_min hboth.1 hboth.2

end
end jacobi.Support
