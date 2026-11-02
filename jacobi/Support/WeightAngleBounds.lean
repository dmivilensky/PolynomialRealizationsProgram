import jacobi.Support.SineShiftBounds
import jacobi.Support.NaturalNodes

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The angular sine factor in the exact support probability grows linearly
with the right-edge index. The uniform comparison includes the first
spectral index and uses the actual original degree-dependent step.
Use: supportWeight_ratio_bounds combines this factor with the exact half-step product formula to prove global original weight estimates.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The actual support angular sine ratio has uniform positive linear bounds throughout the right spectral half.
Use: supportWeight_ratio_bounds combines this factor with the exact half-step product formula to prove global original weight estimates.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: use the same genuine shifted-sine estimate at k+1 and at one, with shift gamma_alpha-1. Their positive original step cancels, giving the stated original index factor. -/
theorem weightAngle_ratio_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀k:ℕ,2*k≤n→
      c*((k:ℝ)+1)≤sin (jacobi.Jacobi.modelAngle a b (n+1) k)/
        sin (jacobi.Jacobi.modelAngle a b (n+1) 0) ∧
      sin (jacobi.Jacobi.modelAngle a b (n+1) k)/
        sin (jacobi.Jacobi.modelAngle a b (n+1) 0)≤C*((k:ℝ)+1) := by
  -- Both sine factors use exactly the same original positive step and endpoint shift.
  have hg := (parameter_pos ha hb).1
  obtain ⟨c,C,hc,hC,hbound⟩ := shifted_sine_bounds a b (show -1<gamma a-1 by linarith) 3
  refine ⟨c/C,C/c,div_pos hc hC,div_pos hC hc,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hbound] with n hn
  intro k hk
  obtain ⟨hdlo,hdhi⟩ := hn.2 1 (by omega) (by omega)
  obtain ⟨hklo,hkhi⟩ := hn.2 (k+1) (by omega) (by omega)
  have hd : 0<sin (gamma a*step a b (n+1)) := by
    have h := (jacobi.Jacobi.modelAngle_endpoint_bounds ha hb (show 0<n+1 by omega)).1
    rw [modelAngle_step] at h
    simp only [Nat.cast_zero,zero_add] at h
    exact sin_pos_of_pos_of_lt_pi h.1 h.2
  have he (x:ℝ) : x+1+(gamma a-1)=x+gamma a := by ring
  simp only [Nat.cast_add,Nat.cast_one,mul_one] at hdlo hdhi hklo hkhi
  rw [show 1+(gamma a-1)=gamma a by ring] at hdlo hdhi
  rw [he] at hklo hkhi
  rw [modelAngle_step,modelAngle_step]
  simp only [Nat.cast_zero,zero_add]
  have hx : 0<(k:ℝ)+1 := by positivity
  have hp : 0<c*((k:ℝ)+1)*step a b (n+1) := mul_pos (mul_pos hc hx) hn.1
  constructor
  · calc
      _ = (c*((k:ℝ)+1)*step a b (n+1))/(C*step a b (n+1)) := by field_simp [hn.1.ne']
      _ ≤ sin (((k:ℝ)+gamma a)*step a b (n+1))/sin (gamma a*step a b (n+1)) :=
        div_le_div₀ (hp.le.trans hklo) hklo hd hdhi
  · calc
      _ ≤ (C*((k:ℝ)+1)*step a b (n+1))/(c*step a b (n+1)) :=
        div_le_div₀ (mul_pos (mul_pos hC hx) hn.1).le hkhi (mul_pos hc hn.1) hdlo
      _ = _ := by field_simp [hn.1.ne']

end
end jacobi.Support
