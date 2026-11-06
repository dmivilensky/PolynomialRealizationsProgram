import nesterov.Oracle.ResistingFrameUnit

/-! Finite adaptive resisting frames, constructed by orthogonalizing against
all previously exposed vectors and queries. -/
namespace nesterov.Oracle
noncomputable section
open Set
open scoped RealInnerProductSpace
variable {E : Type*}

def framePrefix {n : ℕ} (v : Fin n→E) (k : ℕ) (hk : k≤n) : Fin k→E :=
  fun i=>v ⟨i.val,lt_of_lt_of_le i.isLt hk⟩

@[simp] theorem framePrefix_full {n : ℕ} (v : Fin n→E) : framePrefix v n le_rfl=v := by
  funext i
  congr

@[simp] theorem framePrefix_snoc {n k : ℕ} (v : Fin n→E) (w : E) (hk : k≤n) :
    framePrefix (Fin.snoc v w) k (hk.trans (Nat.le_succ n))=framePrefix v k hk := by
  funext i
  change (Fin.snoc (α:=fun _=>E) v w) (Fin.castSucc ⟨i.val,lt_of_lt_of_le i.isLt hk⟩)=_
  rw [Fin.snoc_castSucc]
  rfl

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def GoodFramePrefix (query : (k : ℕ)→(Fin k→E)→E) {n : ℕ} (v : Fin n→E) : Prop :=
  Orthonormal ℝ v ∧ ∀ i j : Fin n,i.val≤j.val →
    inner ℝ (v j) (query i.val (framePrefix v i.val i.isLt.le))=0

theorem goodFramePrefix_extend (query : (k : ℕ)→(Fin k→E)→E)
    {k : ℕ} {v : Fin k→E} (hv : GoodFramePrefix query v)
    (hdim : 2*k+1<Module.finrank ℝ E) :
    ∃ w : E,GoodFramePrefix query (Fin.snoc v w) := by
  let qv : Fin (k+1)→E := Fin.snoc
    (fun i : Fin k=>query i.val (framePrefix v i.val i.isLt.le)) (query k v)
  let forbidden : Sum (Fin k) (Fin (k+1))→E := Sum.elim v qv
  obtain ⟨w,hwn,hw⟩ := exists_unit_orthogonal_finite forbidden (by simp only [Fintype.card_sum,Fintype.card_fin];omega)
  have hwv (i : Fin k) : inner ℝ w (v i)=0 := hw (Sum.inl i)
  have hwq (i : Fin k) : inner ℝ w (query i.val (framePrefix v i.val i.isLt.le))=0 := by
    simpa only [forbidden,Sum.elim_inr,qv,Fin.snoc_castSucc] using hw (Sum.inr i.castSucc)
  have hwlast : inner ℝ w (query k v)=0 := by
    simpa only [forbidden,Sum.elim_inr,qv,Fin.snoc_last] using hw (Sum.inr (Fin.last k))
  refine ⟨w,?_,?_⟩
  · rw [orthonormal_iff_ite]
    intro i
    refine Fin.lastCases ?_ (fun i=>?_) i
    · intro j
      refine Fin.lastCases ?_ (fun j=>?_) j
      · norm_num [Fin.snoc_last,inner_self_eq_norm_sq_to_K,hwn]
      · simp only [Fin.snoc_last,Fin.snoc_castSucc,Ne.symm (Fin.castSucc_ne_last j),ite_false]
        exact hwv j
    · intro j
      refine Fin.lastCases ?_ (fun j=>?_) j
      · simp only [Fin.snoc_last,Fin.snoc_castSucc,Fin.castSucc_ne_last,ite_false]
        rw [real_inner_comm]
        exact hwv i
      · simp only [Fin.snoc_castSucc,Fin.castSucc_inj]
        exact orthonormal_iff_ite.mp hv.1 i j
  · intro i
    refine Fin.lastCases ?_ (fun i=>?_) i
    · intro j hij
      have hj : j=Fin.last k := by apply Fin.ext;dsimp at hij ⊢;omega
      subst j
      simpa only [Fin.snoc_last,Fin.val_last,framePrefix_snoc v w le_rfl,framePrefix_full] using hwlast
    · intro j
      refine Fin.lastCases ?_ (fun j=>?_) j
      · intro _
        simpa only [Fin.snoc_last,Fin.val_castSucc,framePrefix_snoc v w i.isLt.le] using hwq i
      · intro hij
        simpa only [Fin.snoc_castSucc,Fin.val_castSucc,framePrefix_snoc v w i.isLt.le] using hv.2 i j hij

theorem exists_resisting_query_frame (N : ℕ)
    (query : (k : ℕ)→(Fin k→E)→E) (hdim : 2*N+2≤Module.finrank ℝ E) :
    ∃ v : Fin (N+1)→E,GoodFramePrefix query v := by
  have h (k : ℕ) (hk : k≤N+1) : ∃ v : Fin k→E,GoodFramePrefix query v := by
    induction k with
    | zero =>
      refine ⟨Fin.elim0,?_,?_⟩
      · constructor
        · intro i;exact Fin.elim0 i
        · intro i;exact Fin.elim0 i
      · intro i;exact Fin.elim0 i
    | succ k ih =>
      obtain ⟨v,hv⟩ := ih (by omega)
      obtain ⟨w,hw⟩ := goodFramePrefix_extend query hv (by omega)
      exact ⟨Fin.snoc v w,hw⟩
  exact h (N+1) le_rfl

theorem exists_resisting_frame (N : ℕ)
    (query : (k : ℕ)→(Fin k→E)→E) (out : (Fin N→E)→E)
    (hdim : 2*N+2≤Module.finrank ℝ E) :
    ∃ v : Fin (N+1)→E,Orthonormal ℝ v ∧
      (∀ i : Fin N,∀ j : Fin (N+1),i.val≤j.val →
        inner ℝ (v j) (query i.val (framePrefix v i.val (by omega)))=0) ∧
      inner ℝ (v (Fin.last N)) (out (fun i=>v i.castSucc))=0 := by
  let extended : (k : ℕ)→(Fin k→E)→E := fun k u=>
    if hk : k=N then out (fun i=>u ⟨i.val,by omega⟩) else query k u
  obtain ⟨v,hv⟩ := exists_resisting_query_frame N extended hdim
  refine ⟨v,hv.1,?_,?_⟩
  · intro i j hij
    have hi := hv.2 i.castSucc j hij
    simpa only [extended,Fin.val_castSucc,dite_eq_right (ne_of_lt i.isLt)] using hi
  · have hi := hv.2 (Fin.last N) (Fin.last N) le_rfl
    simp only [extended,Fin.val_last,dite_eq_left rfl] at hi
    have hp : (fun i : Fin N=>framePrefix v N (Fin.last N).isLt.le ⟨i.val,by omega⟩)=
        (fun i : Fin N=>v i.castSucc) := by
      funext i
      unfold framePrefix
      congr
    rw [hp] at hi
    exact hi

end
end nesterov.Oracle
