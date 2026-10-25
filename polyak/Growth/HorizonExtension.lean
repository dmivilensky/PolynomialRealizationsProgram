import polyak.Growth.HorizonSegment

/-!
Article: Appendix C, continuation for finite-memory segment arguments.
Use: every finite H-table extends to an infinite H-table. Only a bounded recent
window is interpolated; the future is then a genuine trajectory of that potential.
The earlier table is retained exactly, including its supplied interior values.
-/

namespace polyak.Growth
noncomputable section
open Interpolation

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: one infinite finite-memory interpolation table. -/
structure HRun (A B β : ℝ) (H : ℕ) where
  x : ℕ → E
  σ : ℕ → E
  value : ℕ → ℝ
  interpolation : ∀ i,1 ≤ i → ∀ j,1 ≤ j → Nat.dist i j ≤ H →
    |datumT x σ value i j| ≤ datumR x σ i j
  origin : ∀ i,1 ≤ i → |value i-(1/2 : ℝ)*inner ℝ (σ i) (x i)| ≤
    (1/4 : ℝ)*(‖x i‖^2-‖σ i‖^2)
  recurrence : ∀ k,x (k+2)=A • x (k+1)+B • σ (k+1)-β • x k

variable {E}

def HRun.segment {A B β : ℝ} {H : ℕ} (r : HRun E A B β H) (n : ℕ) :
    HSegment E A B β H n where
  x := r.x
  σ := r.σ
  value := r.value
  interpolation i hi _ j hj _ hij := r.interpolation i hi j hj hij
  origin i hi _ := r.origin i hi
  recurrence k _ := r.recurrence k

/-- Article: infinite finite-memory tables are closed under every consecutive restriction. -/
def HRun.shift {A B β : ℝ} {H : ℕ} (r : HRun E A B β H) (l : ℕ) :
    HRun E A B β H where
  x k := r.x (l+k)
  σ k := r.σ (l+k)
  value k := r.value (l+k)
  interpolation i hi j hj hij := r.interpolation (l+i) (by omega) (l+j) (by omega)
    (by rwa [Nat.dist_add_add_left])
  origin i hi := r.origin (l+i) (by omega)
  recurrence k := by simpa only [Nat.add_assoc] using r.recurrence (l+k)

variable [CompleteSpace E]

/-- Article: every finite H-segment has an infinite continuation, retaining all its actual data.
Only its last at most H interior data are used to interpolate the future potential. -/
theorem HSegment.exists_hRun {A B β : ℝ} {H n : ℕ} (s : HSegment E A B β H n) :
    ∃ r : HRun E A B β H,(∀ k,k ≤ n+1 → r.x k=s.x k) ∧
      ∀ i,1 ≤ i → i ≤ n → r.σ i=s.σ i ∧ r.value i=s.value i := by
  let l := n-H
  let m := n-l
  have hl : l ≤ n := Nat.sub_le _ _
  have hlm : l+m=n := by dsimp only [m]; omega
  have hm : m ≤ H+1 := by dsimp only [m,l]; omega
  let w := s.restrict l m (by omega)
  obtain ⟨r,hpos,hdata⟩ := w.exists_run_of_length_le hm
  have hrecent (k : ℕ) (hk : l ≤ k) (hkn : k ≤ n+1) : r.x (k-l)=s.x k := by
    have hh := hpos (k-l) (by omega)
    change r.x (k-l)=s.x (l+(k-l)) at hh
    simpa only [Nat.add_sub_of_le hk] using hh
  have hrecentData (i : ℕ) (hi : l+1 ≤ i) (hin : i ≤ n) :
      r.ψ (r.x (i-l))=s.value i ∧ gradient r.ψ (r.x (i-l))=s.σ i := by
    have hh := hdata (i-l) (by omega) (by omega)
    change r.ψ (r.x (i-l))=s.value (l+(i-l)) ∧
      gradient r.ψ (r.x (i-l))=s.σ (l+(i-l)) at hh
    simpa only [Nat.add_sub_of_le (show l ≤ i by omega)] using hh
  let X : ℕ → E := fun k => if k ≤ n+1 then s.x k else r.x (k-l)
  let S : ℕ → E := fun k => if k ≤ n then s.σ k else gradient r.ψ (r.x (k-l))
  let V : ℕ → ℝ := fun k => if k ≤ n then s.value k else r.ψ (r.x (k-l))
  have hX (k : ℕ) (hk : l ≤ k) : X k=r.x (k-l) := by
    dsimp only [X]
    split_ifs with hkn
    · exact (hrecent k hk hkn).symm
    · rfl
  have hS (k : ℕ) (hk : l+1 ≤ k) : S k=gradient r.ψ (r.x (k-l)) := by
    dsimp only [S]
    split_ifs with hkn
    · exact (hrecentData k hk hkn).2.symm
    · rfl
  have hV (k : ℕ) (hk : l+1 ≤ k) : V k=r.ψ (r.x (k-l)) := by
    dsimp only [V]
    split_ifs with hkn
    · exact (hrecentData k hk hkn).1.symm
    · rfl
  have hinterp (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : Nat.dist i j ≤ H) :
      |datumT X S V i j| ≤ datumR X S i j := by
    by_cases hin : i ≤ n
    · by_cases hjn : j ≤ n
      · simpa only [datumT,datumR,X,S,V,ite_eq_left hin,ite_eq_left hjn,
          ite_eq_left (show i ≤ n+1 by omega),ite_eq_left (show j ≤ n+1 by omega)] using
          s.interpolation i hi hin j hj hjn hij
      · have hli : l+1 ≤ i := by dsimp only [l]; unfold Nat.dist at hij; omega
        have hlj : l+1 ≤ j := by omega
        have hh := (r.segment (max (i-l) (j-l))).interpolation (i-l) (by omega) (j-l) (by omega)
        simpa only [datumT,datumR,Run.segment,Segment.ofNormalized,hX i (by omega),
          hX j (by omega),hS i hli,hS j hlj,hV i hli,hV j hlj] using hh
    · have hli : l+1 ≤ i := by omega
      have hlj : l+1 ≤ j := by dsimp only [l]; unfold Nat.dist at hij; omega
      have hh := (r.segment (max (i-l) (j-l))).interpolation (i-l) (by omega) (j-l) (by omega)
      simpa only [datumT,datumR,Run.segment,Segment.ofNormalized,hX i (by omega),
        hX j (by omega),hS i hli,hS j hlj,hV i hli,hV j hlj] using hh
  have horigin (i : ℕ) (hi : 1 ≤ i) :
      |V i-(1/2 : ℝ)*inner ℝ (S i) (X i)| ≤ (1/4 : ℝ)*(‖X i‖^2-‖S i‖^2) := by
    by_cases hin : i ≤ n
    · simpa only [X,S,V,ite_eq_left hin,ite_eq_left (show i ≤ n+1 by omega)] using s.origin i hi hin
    · have hh := (r.segment (i-l)).origin (i-l) (by omega)
      have hli : l+1 ≤ i := by omega
      simpa only [Run.segment,Segment.ofNormalized,hX i (by omega),hS i hli,hV i hli] using hh
  have hrec (k : ℕ) : X (k+2)=A • X (k+1)+B • S (k+1)-β • X k := by
    by_cases hkn : k<n
    · simpa only [X,S,ite_eq_left (show k+2 ≤ n+1 by omega),
        ite_eq_left (show k+1 ≤ n+1 by omega),ite_eq_left (show k ≤ n+1 by omega),
        ite_eq_left (show k+1 ≤ n by omega)] using s.recurrence k hkn
    · rw [hX (k+2) (by omega),hX (k+1) (by omega),hX k (by omega),hS (k+1) (by omega)]
      have hlk : l ≤ k := by omega
      rw [show k+2-l=(k-l)+2 by omega,show k+1-l=(k-l)+1 by omega]
      exact r.recurrence (k-l)
  refine ⟨⟨X,S,V,fun i hi j hj hij => hinterp i j hi hj hij,horigin,hrec⟩,?_,?_⟩
  · intro k hk
    exact ite_eq_left hk
  · intro i _ hin
    exact ⟨ite_eq_left hin,ite_eq_left hin⟩

end
end polyak.Growth
