import jacobi.Finite.FreeRecurrenceError
import jacobi.Support.CoefficientBounds
import jacobi.Support.Volterra

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The actual original support polynomial recurrence is a free Jacobi
equation with the printed uniform inverse-square error. Every matrix
coefficient estimate and recurrence premise is discharged here.
Use: the actual oscillatory support envelope applies the proved two-component state propagation to this same original polynomial recurrence.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference jacobi.Finite
open scoped Topology

/-- The genuine original support wave satisfies the source's uniform inverse-square free recurrence error bound at every bounded complex energy.
Use: the actual oscillatory support envelope applies the proved two-component state propagation to this same original polynomial recurrence.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: the actual original coupling lower bound and joint coefficient error bound apply at both adjacent edges and the original diagonal. A shift costs at most four in the same inverse-square denominator. The genuine normalized polynomial recurrence then discharges every premise of the exact free-recurrence error comparison. -/
theorem naturalWave_free_error {a b Y:ℝ} (ha:-1<a) (hb:-1<b) (hY:0≤Y) :
    ∃D:ℝ,0<D ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+3→∀y:ℂ,‖y‖≤Y→
      ‖naturalWave a b ha hb n (m+2) y-2*y*naturalWave a b ha hb n (m+1) y+
          naturalWave a b ha hb n m y‖≤
        D/((m:ℝ)+2)^2*(‖naturalWave a b ha hb n m y‖+‖naturalWave a b ha hb n (m+1) y‖) := by
  -- The original finite chain supplies the same true row and both actual adjacent coefficients used in the free comparison.
  obtain ⟨c,C,hc,hC,hcoeff⟩ := coefficient_bounds ha hb
  refine ⟨((2*Y+2)/c)*(4*C),by positivity,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hcoeff,eventually_ge_atTop (8:ℕ)] with n hn hlarge
  intro m hm y hy
  let J := naturalChain a b ha hb (n+1)
  let ac := fun j => sqrt (J.data.aSq j)
  let v := fun j => naturalWave a b ha hb n j y
  let H := 4*C/((m:ℝ)+2)^2
  have hH : 0≤H := by dsimp [H]; positivity
  have h₁ := hn.2 (m+1) (by omega) (by omega)
  have h₂ := hn.2 (m+2) (by omega) (by omega)
  have hscale : C/((m:ℝ)+1)^2≤H := by
    calc
      _ = C*(1/((m:ℝ)+1)^2) := by ring
      _ ≤ C*(4/((m:ℝ)+2)^2) := mul_le_mul_of_nonneg_left (inverse_square_shift m) hC.le
      _ = H := by dsimp [H]; ring
  have hscale₂ : C/((m:ℝ)+2)^2≤H :=
    div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  have ha₁ : |ac (m+1)-1/2|≤H := by
    have h := (le_add_of_nonneg_right (abs_nonneg (J.data.b (m+1)))).trans h₁.2
    simp only [Nat.cast_add,Nat.cast_one] at h
    exact h.trans hscale
  have ha₂ : |ac (m+2)-1/2|≤H := by
    have h := (le_add_of_nonneg_right (abs_nonneg (J.data.b (m+2)))).trans h₂.2
    simp only [Nat.cast_add,Nat.cast_ofNat] at h
    exact h.trans hscale₂
  have hdiag : |J.data.b (m+1)|≤H := by
    have h := (le_add_of_nonneg_left (abs_nonneg (ac (m+1)-1/2))).trans h₁.2
    simp only [Nat.cast_add,Nat.cast_one] at h
    exact h.trans hscale
  have hrec : (ac (m+2):ℂ)*v (m+2)+(ac (m+1):ℂ)*v m+(J.data.b (m+1):ℂ)*v (m+1)=y*v (m+1) := by
    have h := normalizedLeading_recurrence J (naturalChain_irreducible a b ha hb (n+1)) y (m+1) (by omega)
    simpa only [ac,v,naturalWave,naturalPolynomial,J,Nat.add_assoc,Nat.reduceAdd,Nat.add_sub_cancel,
      ite_eq_right (by omega : m+1≠0)] using h
  have h := free_recurrence_error_bound hc h₂.1 hH hY hy ha₁ ha₂ hdiag hrec
  exact h.trans_eq (by dsimp [H]; ring)

end
end jacobi.Support
