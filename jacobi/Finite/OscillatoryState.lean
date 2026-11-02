import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The two free-wave differences retain the original adjacent polynomial
values. Their exact algebra and norm estimates control the original
perturbed recurrence without a matrix diagonalization assumption.
Source: the elementary free Jacobi transfer equation.
Use: free_state_recovery and free_state_step give the original oscillatory recurrence estimates used in the support envelope.
-/
namespace jacobi.Finite
noncomputable section

/-- The sum of the two actual free-wave difference norms at one adjacent pair.
Use: free_state_recovery and free_state_step give the original oscillatory recurrence estimates used in the support envelope.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
-/
def freeState (q x y:ℂ) : ℝ := ‖y-q*x‖+‖y-q⁻¹*x‖

/-- The genuine adjacent wave values are bounded by their original two-component free-wave state.
Use: the actual support recurrence error is controlled by freeState in the oscillatory envelope.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: subtract the original two differences to recover the first value, and subtract their q-weighted versions to recover the second. The same nonzero spectral gap divides both exact identities. -/
theorem free_state_recovery {q x y:ℂ} {E:ℝ} (hq:q≠0)
    (hgap:0<‖q-q⁻¹‖) (hE:1≤E) (hp:‖q‖≤E) (hm:‖q⁻¹‖≤E) :
    ‖x‖+‖y‖≤(2*E/‖q-q⁻¹‖)*freeState q x y := by
  -- The actual difference identities preserve the original wave values and have only the genuine free spectral gap in the denominator.
  have hx : ‖q-q⁻¹‖*‖x‖≤freeState q x y := by
    rw [← norm_mul]
    have he : (q-q⁻¹)*x=(y-q⁻¹*x)-(y-q*x) := by ring
    rw [he]
    exact (norm_sub_le _ _).trans_eq (add_comm _ _)
  have hy : ‖q-q⁻¹‖*‖y‖≤E*freeState q x y := by
    rw [← norm_mul]
    have he : (q-q⁻¹)*y=q*(y-q⁻¹*x)-q⁻¹*(y-q*x) := by field_simp [hq]; ring
    rw [he]
    calc
      _ ≤ ‖q*(y-q⁻¹*x)‖+‖q⁻¹*(y-q*x)‖ := norm_sub_le _ _
      _ ≤ E*‖y-q⁻¹*x‖+E*‖y-q*x‖ := by
        rw [norm_mul,norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hm (norm_nonneg _))
      _ = _ := by unfold freeState; ring
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hgap).mpr
  have hs : 0≤freeState q x y := by unfold freeState; positivity
  have hsum := add_le_add hx hy
  have h1 := mul_le_mul_of_nonneg_right hE hs
  nlinarith only [hsum,h1]

/-- The actual free-wave state has the original one-step perturbed propagation bound.
Use: free_state_perturbed_step converts the genuine support recurrence's inverse-square error into an integrable multiplicative state estimate.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: the exact two free-wave transfer identities use q*q^(-1)=1. Bound their two genuine source additions by the triangle inequality. -/
theorem free_state_step {q x y z e:ℂ} {E:ℝ} (hq:q≠0)
    (hp:‖q‖≤E) (hm:‖q⁻¹‖≤E) (hz:z=(q+q⁻¹)*y-x+e) :
    freeState q y z≤E*freeState q x y+2*‖e‖ := by
  -- The two original source terms have exactly the same error and opposite free propagation factors.
  have hplus : z-q*y=q⁻¹*(y-q*x)+e := by rw [hz]; field_simp [hq]; ring
  have hminus : z-q⁻¹*y=q*(y-q⁻¹*x)+e := by rw [hz]; field_simp [hq]; ring
  unfold freeState
  rw [hplus,hminus]
  have hp' : ‖q⁻¹*(y-q*x)+e‖≤E*‖y-q*x‖+‖e‖ := by
    calc
      _ ≤ ‖q⁻¹*(y-q*x)‖+‖e‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_right hm (norm_nonneg _)) le_rfl
  have hm' : ‖q*(y-q⁻¹*x)+e‖≤E*‖y-q⁻¹*x‖+‖e‖ := by
    calc
      _ ≤ ‖q*(y-q⁻¹*x)‖+‖e‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) le_rfl
  linarith

/-- The genuine original inverse-square recurrence error gives the printed multiplicative free-state estimate.
Use: the support oscillatory envelope iterates this proved one-step estimate with the actual coefficient-error bound.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: the exact free-state propagation and recovery bounds absorb the actual source error into the same original two-component state. -/
theorem free_state_perturbed_step {q x y z e:ℂ} {E D:ℝ} (hq:q≠0)
    (hgap:0<‖q-q⁻¹‖) (hE:1≤E) (hp:‖q‖≤E) (hm:‖q⁻¹‖≤E) (hD:0≤D)
    (hz:z=(q+q⁻¹)*y-x+e) (he:‖e‖≤D*(‖x‖+‖y‖)) :
    freeState q y z≤E*(1+4*D/‖q-q⁻¹‖)*freeState q x y := by
  have hr := free_state_recovery (x:=x) (y:=y) hq hgap hE hp hm
  have hs := free_state_step hq hp hm hz
  have h := he.trans (mul_le_mul_of_nonneg_left hr hD)
  calc
    _ ≤ E*freeState q x y+2*(D*((2*E/‖q-q⁻¹‖)*freeState q x y)) := by linarith
    _ = _ := by ring

end
end jacobi.Finite
