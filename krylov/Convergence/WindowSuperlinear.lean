import krylov.Convergence.OldestWindowSource

/-!
Article: main_krylov, thm:Ip and thm:ss1F, separation of window ages.
Use: superlinearity of a genuine trajectory makes every fixed positive lag
negligible relative to its oldest point and makes the oldest actual step
asymptotically equal in norm to that point. These are derived sequence facts.
Source: finite composition rules for little-o and the norm triangle inequality.
-/

namespace krylov.Convergence
noncomputable section
open Filter Topology Asymptotics
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E]

/-- Every fixed positive forward lag is negligible on a superlinear tail. -/
theorem superlinear_window_tail (x : ℕ → E)
    (hs : (fun k=>x (k+1)) =o[atTop] (fun k=>‖x k‖)) (j : ℕ) :
    (fun k=>‖x (k+j+1)‖) =o[atTop] (fun k=>‖x k‖) := by
  induction j with
  | zero => simpa only [Nat.add_zero] using hs.norm_left
  | succ j ih =>
    have hh := hs.norm_left.comp_tendsto (tendsto_add_atTop_nat (j+1))
    have hh' : (fun k=>‖x (k+(j+1)+1)‖) =o[atTop] (fun k=>‖x (k+j+1)‖) := by
      simpa only [Function.comp_def,Nat.add_assoc] using hh
    exact hh'.trans_isBigO ih.isBigO

/-- The norm of the actual oldest step differs from the norm of its anchor
by at most the next actual point's norm. -/
theorem window_step_norm_error (x : ℕ → E) (k : ℕ) :
    |‖x (k+1)-x k‖-‖x k‖|≤‖x (k+1)‖ := by
  have hh := abs_norm_sub_norm_le (x (k+1)-x k) (-x k)
  simpa only [norm_neg,sub_neg_eq_add,sub_add_cancel] using hh

/-- Actual nonstationary superlinear steps have precisely the printed
normalization ‖s_k‖/e_k→1. -/
theorem superlinear_window_step_ratio (x : ℕ → E)
    (hs : (fun k=>x (k+1)) =o[atTop] (fun k=>‖x k‖))
    (hne : ∀ᶠ k in atTop,x k≠0) :
    Tendsto (fun k=>‖x (k+1)-x k‖/‖x k‖) atTop (𝓝 1) := by
  have herr : (fun k=>‖x (k+1)-x k‖-‖x k‖) =o[atTop] (fun k=>‖x k‖) := by
    have hb : (fun k=>‖x (k+1)-x k‖-‖x k‖) =O[atTop] (fun k=>‖x (k+1)‖) := by
      apply isBigO_of_le
      intro k
      simpa only [Real.norm_eq_abs,abs_norm] using window_step_norm_error x k
    exact hb.trans_isLittleO hs.norm_left
  have ht := herr.tendsto_div_nhds_zero.const_add 1
  have he : (fun k=>1+(‖x (k+1)-x k‖-‖x k‖)/‖x k‖) =ᶠ[atTop]
      (fun k=>‖x (k+1)-x k‖/‖x k‖) := by
    filter_upwards [hne] with k hk
    field_simp [norm_ne_zero_iff.mpr hk]
    ring
  simpa only [add_zero] using ht.congr' he

/-- The actual total radius of all newer window segments is negligible
relative to the oldest point, in every dimension including an empty newer
window. -/
theorem superlinear_newer_window_radius {n : ℕ} (x : ℕ → E)
    (hs : (fun k=>x (k+1)) =o[atTop] (fun k=>‖x k‖)) :
    (fun k=>newerWindowRadius (fun i : Fin (n+1)=>x (k+i.val))
      (fun i=>x (k+i.val+1))) =o[atTop] (fun k=>‖x k‖) := by
  have hh (i : Fin n) :
      (fun k=>‖x (k+i.succ.val)‖+‖x (k+i.succ.val+1)‖) =o[atTop] (fun k=>‖x k‖) := by
    have h₁ := superlinear_window_tail x hs i.val
    have h₂ := superlinear_window_tail x hs (i.val+1)
    simpa only [Fin.val_succ,Nat.add_assoc] using h₁.add h₂
  have ht := IsLittleO.sum (s:=Finset.univ) (fun i _=>hh i)
  apply ht.congr_left
  intro k
  simp only [newerWindowRadius,Finset.sum_apply]

end
end krylov.Convergence
