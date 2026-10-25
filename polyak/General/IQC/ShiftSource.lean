import polyak.General.IQC.EnergyRate

/-! Appendix D, Lemma weighted shift in its literal source constants.
The hypotheses are the energy bound for the initial trajectory and every
restart; a restart of the same autonomous recursion has the same potential. -/
noncomputable section
namespace polyak.General.IQC
open polyak Growth
variable {E : Type*} [NormedAddCommGroup E]

theorem tail_discountedEnergy (x : ℕ → E) (t : ℝ) (k : ℕ) :
    tailEnergy (discountedEnergy x t) k=
      Real.exp (-2*k*t)*(∑' j,discountedEnergy (fun j => x (k+j)) t j) := by
  rw [←tsum_mul_left]
  apply tsum_congr
  intro j
  unfold discountedEnergy
  rw [←mul_assoc,←Real.exp_add]
  congr 2
  push_cast
  ring

theorem weighted_shift (x : ℕ → E) (previous : E) (t : ℝ)
    {C : ℝ} (hC : 0<C) (hs : Summable (discountedEnergy x t))
    (hinit : (∑' j,discountedEnergy x t j)≤C*(‖x 0‖^2+‖previous‖^2))
    (hrestart : ∀ k : ℕ,(∑' j,discountedEnergy (fun j => x (k+1+j)) t j)≤
      C*(‖x (k+1)‖^2+‖x k‖^2)) (k : ℕ) :
    ‖x k‖^2≤C*(C*max 1 (Real.exp (-2*t))/(1+C*max 1 (Real.exp (-2*t))))^(k/2)*
      Real.exp (2*k*t)*(‖x 0‖^2+‖previous‖^2) := by
  have he (n : ℕ) : Real.exp (-2*((n+1:ℕ):ℝ)*t)=
      Real.exp (-2*t)*Real.exp (-2*n*t):=by
    rw [←Real.exp_add]
    congr 1
    push_cast
    ring
  have hb : ∀ n,tailEnergy (discountedEnergy x t) (n+1)≤
      C*(discountedEnergy x t (n+1)+Real.exp (-2*t)*discountedEnergy x t n):=by
    intro n
    rw [tail_discountedEnergy]
    apply le_trans (mul_le_mul_of_nonneg_left (hrestart n) (Real.exp_pos _).le)
    dsimp [discountedEnergy]
    rw [he]
    ring_nf
    exact le_rfl
  have hh:=weighted_tail_bound hs (discountedEnergy_nonneg x t) hC
    (Real.exp_pos (-2*t)).le hb k
  have hθ : 0≤C*max 1 (Real.exp (-2*t))/(1+C*max 1 (Real.exp (-2*t))):=by positivity
  have htail : tailEnergy (discountedEnergy x t) 0≤C*(‖x 0‖^2+‖previous‖^2):=by
    simpa only [tailEnergy,Nat.zero_add] using hinit
  have hh':=hh.trans (mul_le_mul_of_nonneg_left htail (pow_nonneg hθ (k/2)))
  have hm:=mul_le_mul_of_nonneg_left hh' (Real.exp_pos (2*k*t)).le
  have hc : Real.exp (2*k*t)*Real.exp (-2*k*t)=1:=by
    rw [←Real.exp_add,show 2*(k:ℝ)*t+-2*k*t=0 by ring,Real.exp_zero]
  dsimp only [discountedEnergy] at hm
  rw [←mul_assoc,hc,one_mul] at hm
  nlinarith only [hm]

end polyak.General.IQC
