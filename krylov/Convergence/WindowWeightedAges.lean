import krylov.Convergence.WindowSuperlinear

/-!
Article: main_krylov, thm:ss1F, weighted age remainders including T3=0.
Use: show that the explicit true source remainders are negligible relative
to T3*first-newer error + L3*oldest error squared. Zero weights are handled
without division by either source budget. Source: finite little-o product
rules and nonnegative domination of each genuine weighted error scale.
-/

namespace krylov.Convergence
noncomputable section
open Filter Topology Asymptotics
variable {E : Type*} [NormedAddCommGroup E]

/-- Nonnegative weighted little-o survives adding another nonnegative
scale, including a zero weight. -/
theorem weighted_littleo_nonnegative (f g h : ℕ → ℝ) (hf : f =o[atTop] g)
    {B : ℝ} (hB : 0≤B) (hg : ∀ k,0≤g k) (hh : ∀ k,0≤h k) :
    (fun k=>B*f k) =o[atTop] (fun k=>B*g k+h k) := by
  by_cases hb : B=0
  · refine IsLittleO.of_bound (fun c hc=>?_)
    exact Filter.Eventually.of_forall fun k=>by rw [hb,zero_mul,norm_zero]; positivity
  · have hs := (hf.const_mul_left B).const_mul_right hb
    have hd : (fun k=>B*g k) =O[atTop] (fun k=>B*g k+h k) := by
      apply isBigO_of_le
      intro k
      rw [Real.norm_of_nonneg (mul_nonneg hB (hg k)),
        Real.norm_of_nonneg (add_nonneg (mul_nonneg hB (hg k)) (hh k))]
      exact le_add_of_nonneg_right (hh k)
    exact hs.trans_isBigO hd

/-- Every explicit negligible source term in the sharp value-window bound
is little-o on the actual weighted oldest/newer scale, even T3=0 or L3=0. -/
theorem superlinear_weighted_age_remainders (x : ℕ → E)
    (hs : (fun k=>x (k+1)) =o[atTop] (fun k=>‖x k‖))
    {B L : ℝ} (hB : 0≤B) (hL : 0≤L) :
    ((fun k=>B*‖x (k+2)‖) =o[atTop] (fun k=>B*‖x (k+1)‖+L*‖x k‖^2)) ∧
    ((fun k=>L*‖x k‖*‖x (k+1)‖) =o[atTop] (fun k=>B*‖x (k+1)‖+L*‖x k‖^2)) ∧
    ((fun k=>L*‖x (k+1)‖^2) =o[atTop] (fun k=>B*‖x (k+1)‖+L*‖x k‖^2)) := by
  have h₁ := hs.norm_left
  have h₂ : (fun k=>‖x (k+2)‖) =o[atTop] (fun k=>‖x (k+1)‖) := by
    simpa only [Function.comp_def,Nat.add_assoc] using h₁.comp_tendsto (tendsto_add_atTop_nat 1)
  have ha := weighted_littleo_nonnegative _ _ (fun k=>L*‖x k‖^2) h₂ hB (fun _=>norm_nonneg _)
    (fun _=>mul_nonneg hL (sq_nonneg _))
  have hp : (fun k=>‖x k‖*‖x (k+1)‖) =o[atTop] (fun k=>‖x k‖^2) := by
    simpa only [pow_two,mul_comm] using h₁.mul_isBigO (isBigO_refl (fun k=>‖x k‖) atTop)
  have hsq : (fun k=>‖x (k+1)‖^2) =o[atTop] (fun k=>‖x k‖^2) := by
    simpa only [pow_two] using h₁.mul_isBigO h₁.isBigO
  have hb := weighted_littleo_nonnegative _ _ (fun k=>B*‖x (k+1)‖) hp hL (fun _=>sq_nonneg _)
    (fun _=>mul_nonneg hB (norm_nonneg _))
  have hc := weighted_littleo_nonnegative _ _ (fun k=>B*‖x (k+1)‖) hsq hL (fun _=>sq_nonneg _)
    (fun _=>mul_nonneg hB (norm_nonneg _))
  exact ⟨ha,by simpa only [mul_assoc,add_comm] using hb,by simpa only [add_comm] using hc⟩

end
end krylov.Convergence
