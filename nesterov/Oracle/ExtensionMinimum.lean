import nesterov.Oracle.ExtensionSmooth
import nesterov.Oracle.ExtensionFaces

/-! Verifiable optimality of a simplex vertex gives the actual minimizer
of the globally defined smooth strongly convex extension. -/
namespace nesterov.Oracle.ExtensionData
noncomputable section
open Set
open scoped BigOperators
variable {I E : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Oracle.ExtensionData I E)

theorem support_eq_of_max {y : E} {α : I→ℝ} (hα : α∈Weights I)
    (hm : ∀ β∈Weights I,D.raw y β≤D.raw y α) : D.support y=moment D.slopes α := by
  have hs := D.optimizer_strong y hα
  have hm' := hm (D.optimizer y) (D.optimizer_weights y)
  have hd : ‖moment D.slopes α-D.support y‖^2/(2*(1-D.q))≤0 := by linarith
  have hn : ‖moment D.slopes α-D.support y‖=0 := by
    have hh := (div_le_iff₀ (by linarith [D.q_lt_one] : (0:ℝ)<2*(1-D.q))).mp hd
    simp only [zero_mul] at hh
    nlinarith [norm_nonneg (moment D.slopes α-D.support y)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

omit [DecidableEq I] [Nonempty I] in
theorem raw_difference (y : E) (α β : I→ℝ) :
    D.raw y β-D.raw y α+‖moment D.slopes β-moment D.slopes α‖^2/(2*(1-D.q))=
      inner ℝ (moment D.slopes β-moment D.slopes α)
        (y-(1/(1-D.q)) • moment D.slopes α)+height D.offsets β-height D.offsets α := by
  simp only [raw,inner_sub_left,inner_sub_right,inner_smul_right,norm_sub_sq_real,
    real_inner_self_eq_norm_sq]
  field_simp [(sub_pos.mpr D.q_lt_one).ne']
  ring

omit [DecidableEq I] [Nonempty I] in
theorem weighted_score (y : E) (α β : I→ℝ) :
    ∑ i,β i*D.score y α i=
      inner ℝ (moment D.slopes β) (y-(1/(1-D.q)) • moment D.slopes α)+height D.offsets β := by
  simp only [score,moment,height,sum_inner,real_inner_smul_left,mul_add,Finset.sum_add_distrib]

omit [Nonempty I] in
theorem single_max_of_scores (y : E) (k : I)
    (hscore : ∀ i,D.score y (Pi.single k 1) i≤D.score y (Pi.single k 1) k)
    {β : I→ℝ} (hβ : β∈Weights I) : D.raw y β≤D.raw y (Pi.single k 1) := by
  have hs : ∑ i,β i*D.score y (Pi.single k 1) i≤D.score y (Pi.single k 1) k := by
    calc
      _≤∑ i,β i*D.score y (Pi.single k 1) k :=
        Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hscore i) (hβ.1 i))
      _=_ := by rw [←Finset.sum_mul,hβ.2,one_mul]
  rw [D.weighted_score] at hs
  have hd := D.raw_difference y (Pi.single k 1) β
  simp only [moment_single,height_single,score] at hs hd
  have hn : 0≤‖moment D.slopes β-D.slopes k‖^2/(2*(1-D.q)) :=
    div_nonneg (sq_nonneg _) (by linarith [D.q_lt_one])
  simp only [inner_sub_left] at hd
  linarith

theorem support_single_of_scores (y : E) (k : I)
    (hscore : ∀ i,D.score y (Pi.single k 1) i≤D.score y (Pi.single k 1) k) :
    D.support y=D.slopes k := by
  have h := D.support_eq_of_max (weights_single k) (fun _ hβ=>D.single_max_of_scores y k hscore hβ)
  simpa only [moment_single] using h

variable [CompleteSpace E]

theorem stationary_of_single_scores (y : E) (k : I)
    (hscore : ∀ i,D.score y (Pi.single k 1) i≤D.score y (Pi.single k 1) k)
    (hzero : D.q • y+D.slopes k=0) : gradient D.potential y=0 := by
  rw [D.gradient_eq,field,D.support_single_of_scores y k hscore]
  exact hzero

theorem isMinOn_of_single_scores (y : E) (k : I)
    (hscore : ∀ i,D.score y (Pi.single k 1) i≤D.score y (Pi.single k 1) k)
    (hzero : D.q • y+D.slopes k=0) : IsMinOn D.potential univ y := by
  intro z _
  have h := D.potential_lower y z
  have hz := D.stationary_of_single_scores y k hscore hzero
  rw [←D.gradient_eq,hz,inner_zero_left,add_zero] at h
  have hn := mul_nonneg (show 0≤D.q/2 by linarith [D.q_pos]) (sq_nonneg ‖z-y‖)
  exact (le_add_of_nonneg_right hn).trans h

end
end nesterov.Oracle.ExtensionData
