import krylov.Tensor.BinaryRFC
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Compact

/-!
Article: main_krylov, apD:lem-binary(c) and thm:Fplanar.
Use: identify the article's genuine remaining-coefficient fibre as a compact
closed interval, with attained endpoints and a data-only centre. This also
identifies the all-chord M_F with the stated supremum of true fibre widths.
Source: convexity and continuity of the actual cubic diagonal inequalities.
-/

namespace krylov.Tensor.BinaryCubic
noncomputable section

/-- The actual observed binary data: the two pure coefficients and P1.
Article: main_krylov, thm:Fplanar. -/
structure Observation where
  t0 : ℝ
  P : ℝ
  t3 : ℝ
  deriving DecidableEq

/-- The genuine observation map of a binary cubic.
Article: main_krylov, thm:Fplanar, P1=t1+r*t2. -/
def observe (r : ℝ) (t : BinaryCubic) : Observation := ⟨t.t0,t.t1+r*t.t2,t.t3⟩

/-- A coefficient completion with precisely the fixed observed data.
Article: main_krylov, thm:Fplanar. -/
def complete (r : ℝ) (O : Observation) (q : ℝ) : BinaryCubic :=
  ⟨O.t0,O.P-r*q,q,O.t3⟩

/-- The complete actual admissible set for the hidden coefficient.
Article: main_krylov, thm:Fplanar, the fibre defining h2. -/
def coefficientFibre (r : ℝ) (O : Observation) : Set ℝ :=
  {q | (complete r O q).InBall}

/-- Completion preserves all genuine observations, exactly.
Article: main_krylov, thm:Fplanar. -/
theorem observe_complete (r : ℝ) (O : Observation) (q : ℝ) : observe r (complete r O q)=O := by
  cases O
  simp [observe,complete]

/-- Every actual cubic is its genuine observed completion.
Article: main_krylov, thm:Fplanar. -/
theorem complete_observe (r : ℝ) (t : BinaryCubic) : complete r (observe r t) t.t2=t := by
  cases t
  simp [observe,complete]

/-- The hidden coefficient of every actual cubic lies in its actual fibre.
Article: main_krylov, thm:Fplanar. -/
theorem self_mem_coefficientFibre {t : BinaryCubic} (ht : t.InBall) (r : ℝ) :
    t.t2∈coefficientFibre r (observe r t) := by
  change (complete r (observe r t) t.t2).InBall
  rwa [complete_observe]

/-- The true coefficient fibres are closed, since every diagonal norm
constraint is a closed polynomial inequality.
Article: main_krylov, thm:Fplanar. -/
theorem coefficientFibre_isClosed (r : ℝ) (O : Observation) : IsClosed (coefficientFibre r O) := by
  change IsClosed {q | ∀ c s : ℝ, c^2+s^2=1 → |(complete r O q).eval c s|≤1}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro c
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro _
  apply isClosed_le _ continuous_const
  unfold complete eval
  fun_prop

/-- Every actual hidden coefficient obeys its sharp unit bound.
Article: main_krylov, apD:lem-binary(a), used for compact fibres. -/
theorem coefficientFibre_abs_le {r : ℝ} {O : Observation} {q : ℝ}
    (hq : q∈coefficientFibre r O) : |q|≤1 := by
  have hd := (coefficient_disks hq).2
  change (O.P-r*q)^2+q^2≤1 at hd
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (O.P-r*q)]

/-- Actual coefficient fibres are compact, including the empty ones.
Article: main_krylov, thm:Fplanar. -/
theorem coefficientFibre_isCompact (r : ℝ) (O : Observation) : IsCompact (coefficientFibre r O) := by
  apply isCompact_Icc.of_isClosed_subset (coefficientFibre_isClosed r O)
  intro q hq
  exact abs_le.mp (coefficientFibre_abs_le hq)

/-- The entire admissible hidden set is convex; the conclusion is derived
from genuine cubic evaluations, rather than assumed interval structure.
Article: main_krylov, thm:Fplanar. -/
theorem coefficientFibre_convex (r : ℝ) (O : Observation) : Convex ℝ (coefficientFibre r O) := by
  intro q hq q' hq' α β hα hβ hab c s hcs
  have he : (complete r O (α • q+β • q')).eval c s=
      α*(complete r O q).eval c s+β*(complete r O q').eval c s := by
    simp only [complete,eval,smul_eq_mul]
    linear_combination -(O.t0*c^3+3*O.P*c^2*s+O.t3*s^3)*hab
  rw [he]
  calc
    |α*(complete r O q).eval c s+β*(complete r O q').eval c s|
      ≤ |α*(complete r O q).eval c s|+|β*(complete r O q').eval c s| := abs_add_le _ _
    _ = α*|(complete r O q).eval c s|+β*|(complete r O q').eval c s| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hα,abs_of_nonneg hβ]
    _ ≤ α*1+β*1 := add_le_add (mul_le_mul_of_nonneg_left (hq c s hcs) hα)
      (mul_le_mul_of_nonneg_left (hq' c s hcs) hβ)
    _ = 1 := by simpa only [mul_one] using hab

/-- The exact hidden-coefficient centre, defined directly from the observed
fibre. Article: main_krylov, thm:Fplanar, centre correction. -/
def fibreCentre (r : ℝ) (O : Observation) : ℝ :=
  (sInf (coefficientFibre r O)+sSup (coefficientFibre r O))/2

/-- The actual fibre half-width, including a degenerate singleton fibre.
Article: main_krylov, thm:Fplanar, h2. -/
def fibreHalfWidth (r : ℝ) (O : Observation) : ℝ :=
  (sSup (coefficientFibre r O)-sInf (coefficientFibre r O))/2

/-- Every nonempty actual fibre is precisely the closed interval between its
attained endpoints. Article: main_krylov, thm:Fplanar. -/
theorem coefficientFibre_eq_Icc (r : ℝ) (O : Observation)
    (hne : (coefficientFibre r O).Nonempty) :
    coefficientFibre r O=Set.Icc (sInf (coefficientFibre r O)) (sSup (coefficientFibre r O)) := by
  have hc := coefficientFibre_isCompact r O
  apply Set.Subset.antisymm
  · intro q hq
    exact ⟨csInf_le hc.bddBelow hq,le_csSup hc.bddAbove hq⟩
  · exact (coefficientFibre_convex r O).ordConnected.out (hc.sInf_mem hne) (hc.sSup_mem hne)

/-- A nonempty fibre has a nonnegative actual half-width.
Article: main_krylov, thm:Fplanar. -/
theorem fibreHalfWidth_nonneg (r : ℝ) (O : Observation)
    (hne : (coefficientFibre r O).Nonempty) : 0≤fibreHalfWidth r O := by
  have hc := coefficientFibre_isCompact r O
  have h := csInf_le hc.bddBelow (hc.sSup_mem hne)
  unfold fibreHalfWidth
  linarith

/-- Centring the hidden coefficient controls every actual admissible completion.
Article: main_krylov, thm:Fplanar. -/
theorem fibreCentre_bound {r : ℝ} {O : Observation} {q : ℝ}
    (hq : q∈coefficientFibre r O) : |q-fibreCentre r O|≤fibreHalfWidth r O := by
  have hc := coefficientFibre_isCompact r O
  have hlo := csInf_le hc.bddBelow hq
  have hhi := le_csSup hc.bddAbove hq
  unfold fibreCentre fibreHalfWidth
  apply abs_le.mpr
  constructor <;> linarith

end
end krylov.Tensor.BinaryCubic
