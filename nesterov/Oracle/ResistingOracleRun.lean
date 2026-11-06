import nesterov.Oracle.ResistingOraclePrefix

/-! The adaptive transcript produced by partial-frame replies agrees with
the actual full-frame oracle transcript, at every permitted horizon. -/
namespace nesterov.Oracle
noncomputable section
open Set
open scoped RealInnerProductSpace
variable {J E : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : ℕ} (D : ExtensionData J (EuclideanSpace ℝ (Fin (N+1)))) (A : Policy E)

def frameQuery (k : ℕ) (u : Fin k→E) : E := A.point (fakeOraclePrefix D u) k

def frameOutput (u : Fin N→E) : E := A.result (fakeOraclePrefix D u) N

theorem fakeOracle_query_agreement (v : Fin (N+1)→E)
    (hchain : ∀ (j : Fin (N+1)) (y : EuclideanSpace ℝ (Fin (N+1))),
      (∀ m,j.val≤m.val → y m=0) → ∀ m,j.val<m.val → D.support y m=0)
    (hq : ∀ i : Fin N,∀ j : Fin (N+1),i.val≤j.val →
      inner ℝ (v j) (frameQuery D A i.val (framePrefix v i.val (by omega)))=0)
    (i : Fin N) {k : ℕ} (hik : i.val<k) (hk : k≤N+1) :
    fakeOraclePrefix D (framePrefix v k hk)
      (frameQuery D A i.val (framePrefix v i.val (by omega)))=
    fakeOraclePrefix D v (frameQuery D A i.val (framePrefix v i.val (by omega))) := by
  let x := frameQuery D A i.val (framePrefix v i.val (by omega))
  have hx : ∀ j : Fin (N+1),i.val≤j.val → inner ℝ (v j) x=0 := hq i
  have hy : ∀ m : Fin (N+1),i.castSucc.val≤m.val → frameCoordinates v x m=0 := hx
  have hs := hchain i.castSucc (frameCoordinates v x) hy
  exact fakeOraclePrefix_agrees_full D hk hik hx hs

theorem frame_run_agreement (v : Fin (N+1)→E)
    (hchain : ∀ (j : Fin (N+1)) (y : EuclideanSpace ℝ (Fin (N+1))),
      (∀ m,j.val≤m.val → y m=0) → ∀ m,j.val<m.val → D.support y m=0)
    (hq : ∀ i : Fin N,∀ j : Fin (N+1),i.val≤j.val →
      inner ℝ (v j) (frameQuery D A i.val (framePrefix v i.val (by omega)))=0) :
    ∀ k : ℕ,∀ hk : k≤N,A.run (fakeOraclePrefix D v) k=
      A.run (fakeOraclePrefix D (framePrefix v k (hk.trans (Nat.le_succ N)))) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    apply A.run_eq_of_answers
    intro i hi
    have hip := ih i hi (by omega)
    have hpoint : A.point (fakeOraclePrefix D v) i=
        frameQuery D A i (framePrefix v i (by omega)) := by
      unfold frameQuery Policy.point
      rw [hip]
    rw [hpoint]
    exact (fakeOracle_query_agreement D A v hchain hq (⟨i,by omega⟩ : Fin N) hi
      (hk.trans (Nat.le_succ N))).symm

variable [FiniteDimensional ℝ E]

theorem exists_orthogonal_oracle_frame
    (hchain : ∀ (j : Fin (N+1)) (y : EuclideanSpace ℝ (Fin (N+1))),
      (∀ m,j.val≤m.val → y m=0) → ∀ m,j.val<m.val → D.support y m=0)
    (hdim : 2*N+2≤Module.finrank ℝ E) :
    ∃ v : Fin (N+1)→E,Orthonormal ℝ v ∧
      inner ℝ (v (Fin.last N))
        (A.result (firstOrderOracle (D.embed v).potential) N)=0 := by
  obtain ⟨v,hv,hq,ho⟩ := exists_resisting_frame N (frameQuery D A) (frameOutput D A) hdim
  have hr := frame_run_agreement D A v hchain hq N le_rfl
  have hresult : A.result (fakeOraclePrefix D v) N=
      frameOutput D A (framePrefix v N (Nat.le_succ N)) := by
    unfold frameOutput Policy.result
    rw [hr]
  refine ⟨v,hv,?_⟩
  rw [←fakeOraclePrefix_is_oracle D hv,hresult]
  have hp : (fun i : Fin N=>v i.castSucc)=framePrefix v N (Nat.le_succ N) := by
    funext i
    congr
  rwa [hp] at ho

end
end nesterov.Oracle
