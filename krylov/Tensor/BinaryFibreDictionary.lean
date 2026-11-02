import krylov.Tensor.BinaryInterval

/-!
Article: main_krylov, thm:Fplanar, exact equivalence of the two M_F formulas.
Use: identify the all-chord coefficient already analyzed with the article's
supremum of |P1| times the actual remaining interval half-width. All endpoints
are true admissible tensors. Source: the proved compact interval fibres.
-/

namespace krylov.Tensor.BinaryCubic
noncomputable section

/-- The exact information radius factor belonging to one observed fibre.
Article: main_krylov, thm:Fplanar, |P1| *h2. -/
def fibreProduct (r : ℝ) (O : Observation) : ℝ := |O.P| *fibreHalfWidth r O

/-- The two genuine endpoint completions form an admissible observation chord.
Article: main_krylov, thm:Fplanar. -/
theorem fibre_endpoints_chord (r : ℝ) (O : Observation)
    (hne : (coefficientFibre r O).Nonempty) :
    Chord r (complete r O (sSup (coefficientFibre r O)))
      (complete r O (sInf (coefficientFibre r O))) := by
  have hc := coefficientFibre_isCompact r O
  refine ⟨hc.sSup_mem hne,hc.sInf_mem hne,rfl,rfl,?_⟩
  dsimp only [complete]
  ring

/-- The actual endpoint chord objective equals the full fibre half-width factor.
Article: main_krylov, thm:Fplanar. -/
theorem fibre_endpoints_value (r : ℝ) (O : Observation)
    (hne : (coefficientFibre r O).Nonempty) :
    chordValue r (complete r O (sSup (coefficientFibre r O)))
      (complete r O (sInf (coefficientFibre r O)))=fibreProduct r O := by
  have hc := coefficientFibre_isCompact r O
  have hlo := csInf_le hc.bddBelow (hc.sSup_mem hne)
  simp only [chordValue,complete,sub_add_cancel,fibreProduct,fibreHalfWidth]
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  ring

/-- Every full actual fibre factor is bounded by the genuine all-chord minimax.
Article: main_krylov, thm:Fplanar. -/
theorem fibreProduct_le_minimax (r : ℝ) (O : Observation)
    (hne : (coefficientFibre r O).Nonempty) : fibreProduct r O≤fibreMinimax r := by
  rw [← fibre_endpoints_value r O hne]
  exact le_csSup (chordValues_bddAbove r) ⟨_,_,fibre_endpoints_chord r O hne,rfl⟩

/-- True chords carry exactly identical actual observations.
Article: main_krylov, thm:Fplanar, binary observation dictionary. -/
theorem chord_observations {r : ℝ} {y z : BinaryCubic} (h : Chord r y z) :
    observe r y=observe r z := by
  obtain ⟨_,_,h0,h3,hP⟩ := h
  unfold observe
  rw [h0,h3,hP]

/-- Every observation chord is bounded by its actual entire fibre width.
Article: main_krylov, thm:Fplanar. -/
theorem chordValue_le_fibreProduct {r : ℝ} {y z : BinaryCubic} (h : Chord r y z) :
    chordValue r y z≤fibreProduct r (observe r y) := by
  have hy := self_mem_coefficientFibre h.1 r
  have hz := self_mem_coefficientFibre h.2.1 r
  rw [← chord_observations h] at hz
  have hc := coefficientFibre_isCompact r (observe r y)
  have hylo := csInf_le hc.bddBelow hy
  have hyhi := le_csSup hc.bddAbove hy
  have hzlo := csInf_le hc.bddBelow hz
  have hzhi := le_csSup hc.bddAbove hz
  have hd : |y.t2-z.t2|≤sSup (coefficientFibre r (observe r y))-sInf (coefficientFibre r (observe r y)) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hm := mul_le_mul_of_nonneg_left hd (abs_nonneg (y.t1+r*y.t2))
  change |y.t1+r*y.t2| * |y.t2-z.t2|/2≤|y.t1+r*y.t2| *
    ((sSup (coefficientFibre r (observe r y))-sInf (coefficientFibre r (observe r y)))/2)
  nlinarith only [hm]

/-- All true fibre half-width factors, with the full observed-data domain.
Article: main_krylov, thm:Fplanar. -/
def fibreProducts (r : ℝ) : Set ℝ :=
  {v | ∃ O : Observation, (coefficientFibre r O).Nonempty ∧ v=fibreProduct r O}

/-- The true fibre objective domain is nonempty, because the zero cubic is feasible.
Article: main_krylov, thm:Fplanar. -/
theorem fibreProducts_nonempty (r : ℝ) : (fibreProducts r).Nonempty := by
  have hz := self_mem_coefficientFibre zero_inBall r
  exact ⟨_,observe r ⟨0,0,0,0⟩,⟨0,hz⟩,rfl⟩

/-- The entire actual fibre objective domain has a genuine finite upper bound.
Article: main_krylov, thm:Fplanar. -/
theorem fibreProducts_bddAbove (r : ℝ) : BddAbove (fibreProducts r) := by
  refine ⟨fibreMinimax r,?_⟩
  rintro v ⟨O,hne,rfl⟩
  exact fibreProduct_le_minimax r O hne

/-- The actual all-chord coefficient is exactly the article's supremum over
all observed fibres of |P1| times their true interval half-width.
Article: main_krylov, thm:Fplanar, equivalence of both displayed M_F definitions.
Proof: every fibre's attained endpoints are an admissible chord; every
admissible chord lies inside its actual entire observed fibre. -/
theorem fibreMinimax_eq_fibreProducts (r : ℝ) : fibreMinimax r=sSup (fibreProducts r) := by
  apply le_antisymm
  · apply csSup_le ⟨0,zero_mem_chordValues r⟩
    rintro v ⟨y,z,h,rfl⟩
    exact (chordValue_le_fibreProduct h).trans (le_csSup (fibreProducts_bddAbove r)
      ⟨observe r y,⟨y.t2,self_mem_coefficientFibre h.1 r⟩,rfl⟩)
  · apply csSup_le (fibreProducts_nonempty r)
    rintro v ⟨O,hne,rfl⟩
    exact fibreProduct_le_minimax r O hne

end
end krylov.Tensor.BinaryCubic
