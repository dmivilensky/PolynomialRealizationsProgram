import jacobi.Support.FreeRecurrenceError
import jacobi.Support.FrequencyGeometry
import jacobi.Finite.OscillatoryPropagation

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The genuine support-wave free state propagates from any actual
transition index with the source's uniform exponential error bound.
Every original coefficient, recurrence and sine-gap estimate is proved.
Use: naturalWave_state_propagation estimates the true oscillatory polynomial state, and the final frequency envelope recovers its original polynomial values.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference jacobi.Finite
open scoped Topology

/-- The genuine support free-wave state at its actual original frequency and adjacent physical coordinates.
Use: naturalWave_state_propagation estimates the true oscillatory polynomial state, and the final frequency envelope recovers its original polynomial values.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
-/
def naturalState (a b:ℝ) (ha:-1<a) (hb:-1<b) (n m:ℕ) (theta:ℂ) : ℝ :=
  freeState (Complex.exp (theta*Complex.I))
    (naturalWave a b ha hb n m (Complex.cos theta))
    (naturalWave a b ha hb n (m+1) (Complex.cos theta))

/-- The actual original support-wave free state has the full source oscillatory propagation bound from any genuine transition coordinate.
Use: the global support envelope inserts the actual transition-state bound and the original theta*(m_0+1)>=1 to obtain the frequency decay.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: the actual polynomial recurrence has the proved inverse-square error at the same bounded complex energy. The exact original free exponential factors and positive sine gap give its multiplicative state inequality. The proved finite telescoping Gronwall estimate sums that genuine error, and the original sector sine lower bound gives the printed frequency denominator. -/
theorem naturalWave_state_propagation {a b bnd:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀theta:ℂ,theta≠0→|theta.re|≤4*π/5→
      |theta.im|≤bnd→|theta.im|≤‖theta‖/2→∀L M:ℕ,L≤M→2*M≤n+3→
        naturalState a b ha hb n M theta≤naturalState a b ha hb n L theta*
          exp (|theta.im| *((M-L:ℕ):ℝ)+C/(‖theta‖*((L:ℝ)+1))) := by
  -- The same original polynomial and actual recurrence are retained throughout the finite state propagation.
  obtain ⟨D,hD,herror⟩ := naturalWave_free_error ha hb (Y:=exp bnd) (exp_pos _).le
  obtain ⟨c,hc,hsine⟩ := oscillatory_sine_lower
  refine ⟨2*D/c,by positivity,?_⟩
  filter_upwards [herror] with n hn
  intro theta htheta hre him hsector L M hLM hM
  let q := Complex.exp (theta*Complex.I)
  let v := fun j => naturalWave a b ha hb n j (Complex.cos theta)
  let s := fun j => naturalState a b ha hb n j theta
  let gap := ‖q-q⁻¹‖
  have hq : q≠0 := Complex.exp_ne_zero _
  have ht : 0<‖theta‖ := norm_pos_iff.mpr htheta
  have hgaplo : 2*c*‖theta‖≤gap := by
    dsimp only [gap,q]
    rw [free_frequency_gap]
    linarith [hsine theta hre hsector]
  have hgap : 0<gap := (by positivity : 0<2*c*‖theta‖).trans_le hgaplo
  have hqnorm := free_frequency_norms theta
  have hy : ‖Complex.cos theta‖≤exp bnd :=
    (jacobi.Reference.cosine_norm_bound theta).trans (exp_le_exp.mpr him)
  have hs (j:ℕ) (hLj:L≤j) (hj:j<M) :
      s (j+1)≤exp (|theta.im|)*(1+(4*D/gap)/((j:ℝ)+2)^2)*s j := by
    let e := v (j+2)-2*Complex.cos theta*v (j+1)+v j
    have hcos : q+q⁻¹=2*Complex.cos theta := by
      dsimp [q]
      rw [← Complex.exp_neg,show -(theta*Complex.I)=(-theta)*Complex.I by ring,
        Complex.exp_mul_I,Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg]
      ring
    have hz : v (j+2)=(q+q⁻¹)*v (j+1)-v j+e := by rw [hcos]; dsimp [e]; ring
    have he : ‖e‖≤(D/((j:ℝ)+2)^2)*(‖v j‖+‖v (j+1)‖) := hn j (by omega) _ hy
    have h := free_state_perturbed_step hq hgap hqnorm.1 hqnorm.2.1 hqnorm.2.2 (by positivity) hz he
    exact h.trans_eq (by dsimp [s,naturalState,gap]; ring)
  have h := inverse_square_propagation s L M hLM (rho:=|theta.im|) (A:=4*D/gap)
    (by positivity) (fun j _ => by dsimp [s,naturalState,freeState]; positivity) hs
  have hratio : (4*D/gap)/((L:ℝ)+1)≤(2*D/c)/(‖theta‖*((L:ℝ)+1)) := by
    calc
      _ ≤ (4*D/(2*c*‖theta‖))/((L:ℝ)+1) :=
        div_le_div_of_nonneg_right (div_le_div₀ (by positivity) le_rfl (by positivity) hgaplo) (by positivity)
      _ = _ := by field_simp; ring
  exact h.trans (mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (add_le_add le_rfl hratio)) (by dsimp [s,naturalState,freeState]; positivity))

end
end jacobi.Support
