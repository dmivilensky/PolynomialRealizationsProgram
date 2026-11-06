import nesterov.Oracle.ExtensionData

/-! First-order optimality of the actual finite-simplex maximizer,
including exact support exclusion under a strict separating score. -/
namespace nesterov.Oracle.ExtensionData
noncomputable section
open Set
open scoped BigOperators
variable {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Oracle.ExtensionData I E)

def score (y : E) (α : I→ℝ) (i : I) : ℝ :=
  inner ℝ (D.slopes i) (y-(1/(1-D.q)) • moment D.slopes α)+D.offsets i

def meanScore (y : E) (α : I→ℝ) : ℝ :=
  inner ℝ (moment D.slopes α) (y-(1/(1-D.q)) • moment D.slopes α)+height D.offsets α

theorem score_gap (y : E) (α : I→ℝ) (i : I) :
    D.score y α i-D.meanScore y α=
      D.raw y (Pi.single i 1)-D.raw y α+
        ‖D.slopes i-moment D.slopes α‖^2/(2*(1-D.q)) := by
  simp only [score,meanScore,raw,moment_single,height_single,inner_sub_right,
    inner_smul_right,norm_sub_sq_real,real_inner_self_eq_norm_sq]
  field_simp [(sub_pos.mpr D.q_lt_one).ne']
  ring

omit [DecidableEq I] in
theorem meanScore_eq_sum (y : E) (α : I→ℝ) :
    D.meanScore y α=∑ i,α i*D.score y α i := by
  simp only [meanScore,score,moment,height,sum_inner,real_inner_smul_left,
    mul_add,Finset.sum_add_distrib]

theorem score_le_mean {y : E} {α : I→ℝ} (hα : α∈Weights I)
    (hm : ∀ β∈Weights I,D.raw y β≤D.raw y α) (i : I) : D.score y α i≤D.meanScore y α := by
  have h := D.max_strong hα hm (weights_single i)
  rw [moment_single] at h
  have he := D.score_gap y α i
  linarith

theorem support_score_eq {y : E} {α : I→ℝ} (hα : α∈Weights I)
    (hm : ∀ β∈Weights I,D.raw y β≤D.raw y α) {k : I} (hk : 0<α k) :
    D.score y α k=D.meanScore y α := by
  have hn (i : I) : 0≤α i*(D.meanScore y α-D.score y α i) :=
    mul_nonneg (hα.1 i) (sub_nonneg.mpr (D.score_le_mean hα hm i))
  have hs : ∑ i,α i*(D.meanScore y α-D.score y α i)=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hα.2,one_mul,←D.meanScore_eq_sum,sub_self]
  have hh := Finset.single_le_sum (fun i _=>hn i) (Finset.mem_univ k)
  rw [hs] at hh
  have hz : α k*(D.meanScore y α-D.score y α k)=0 := le_antisymm hh (hn k)
  have he := (mul_eq_zero.mp hz).resolve_left hk.ne'
  linarith

theorem support_zero_of_score_lt {y : E} {α : I→ℝ} (hα : α∈Weights I)
    (hm : ∀ β∈Weights I,D.raw y β≤D.raw y α) {j k : I}
    (hscore : D.score y α k<D.score y α j) : α k=0 := by
  by_contra hn
  have hp : 0<α k := lt_of_le_of_ne (hα.1 k) (Ne.symm hn)
  have he := D.support_score_eq hα hm hp
  have hl := D.score_le_mean hα hm j
  linarith

omit [DecidableEq I] in
theorem score_lt_of_separation {y : E} {α : I→ℝ} (hα : α∈Weights I) {j k : I}
    (horder : ∀ i,D.offsets k-inner ℝ (D.slopes k) (D.slopes i)/(1-D.q)≤
      D.offsets j-inner ℝ (D.slopes j) (D.slopes i)/(1-D.q))
    (hsep : 0< inner ℝ (D.slopes j-D.slopes k) y) : D.score y α k<D.score y α j := by
  have hi (i : I) : inner ℝ (D.slopes j-D.slopes k) (D.slopes i)/(1-D.q)≤
      D.offsets j-D.offsets k := by
    have h := horder i
    simp only [inner_sub_left,sub_div]
    linarith
  have hm : inner ℝ (D.slopes j-D.slopes k) (moment D.slopes α)/(1-D.q)≤
      D.offsets j-D.offsets k := by
    calc
      _=∑ i,α i*(inner ℝ (D.slopes j-D.slopes k) (D.slopes i)/(1-D.q)) := by
        simp only [moment,inner_sum,inner_smul_right,Finset.sum_div,mul_div_assoc]
      _≤∑ i,α i*(D.offsets j-D.offsets k) :=
        Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hi i) (hα.1 i))
      _=D.offsets j-D.offsets k := by rw [←Finset.sum_mul,hα.2,one_mul]
  dsimp only [score]
  simp only [inner_sub_left,sub_div] at hm hsep
  simp only [inner_sub_right,inner_smul_right]
  simp only [div_eq_mul_inv,one_mul] at hm ⊢
  nlinarith

variable [Nonempty I]

theorem optimizer_zero_of_separation {y : E} {j k : I}
    (horder : ∀ i,D.offsets k-inner ℝ (D.slopes k) (D.slopes i)/(1-D.q)≤
      D.offsets j-inner ℝ (D.slopes j) (D.slopes i)/(1-D.q))
    (hsep : 0< inner ℝ (D.slopes j-D.slopes k) y) : D.optimizer y k=0 :=
  D.support_zero_of_score_lt (D.optimizer_weights y) (D.optimizer_max y)
    (D.score_lt_of_separation (D.optimizer_weights y) horder hsep)

end
end nesterov.Oracle.ExtensionData
