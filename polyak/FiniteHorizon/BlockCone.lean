import polyak.Growth.GramRealization

/-!
Article: Appendix C, closed finite blocks for the compactness step of nearkernel.
Use: a single global Gram matrix retains every bounded-memory interpolation
inequality. Its realization gives a genuine H-segment in a fixed finite dimension.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Interpolation Matrix
open scoped Topology Matrix.Norms.Elementwise

def blockCone (A B β : ℝ) (H n : ℕ) : Set (WindowSpace n) :=
  {Y | Y.1.PosSemidef ∧ (∀ i : Fin n,|starT A B β i Y|≤starR A B β i Y) ∧
    ∀ i j : Fin n,Nat.dist i.val j.val≤H → |pairT A B β i j Y|≤pairR A B β i j Y}

theorem blockCone_isClosed (A B β : ℝ) (H n : ℕ) : IsClosed (blockCone A B β H n) := by
  have hG : IsClosed {Y : WindowSpace n | Y.1.PosSemidef}:=
    Matrix.posSemidef_is_closed.preimage continuous_fst
  have hs : IsClosed {Y : WindowSpace n | ∀ i : Fin n,|starT A B β i Y|≤starR A B β i Y} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (starT A B β i).continuous.abs (starR A B β i).continuous
  have hp : IsClosed {Y : WindowSpace n | ∀ i j : Fin n,Nat.dist i.val j.val≤H →
      |pairT A B β i j Y|≤pairR A B β i j Y} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (pairT A B β i j).continuous.abs (pairR A B β i j).continuous
  exact hG.inter (hs.inter hp)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every element of the global block cone is an actual finite-memory segment. -/
def segmentOfBlock {A B β : ℝ} {H n : ℕ} (hB : B≠0) {Y : WindowSpace n}
    (hY : Y∈blockCone A B β H n) (x : Fin (n+2) → E) (hgram : Matrix.gram ℝ x=Y.1) :
    HSegment E A B β H n where
  x:=realizedPosition x
  σ:=realizedGradient x A B β
  value:=realizedValue Y.2
  interpolation i hi hin j hj hjn hij:=by
    let I : Fin n:=⟨i-1,by omega⟩
    let J : Fin n:=⟨j-1,by omega⟩
    have hI : (I : ℕ)+1=i:=by dsimp [I]; omega
    have hJ : (J : ℕ)+1=j:=by dsimp [J]; omega
    have hposI : realizedPosition x i=x I.castSucc.succ:=by rw [←hI]; exact realizedPosition_fin x I.castSucc.succ
    have hposJ : realizedPosition x j=x J.castSucc.succ:=by rw [←hJ]; exact realizedPosition_fin x J.castSucc.succ
    have hgradI : realizedGradient x A B β i=reconstructedGradient x A B β I:=by rw [←hI,realizedGradient_succ]
    have hgradJ : realizedGradient x A B β j=reconstructedGradient x A B β J:=by rw [←hJ,realizedGradient_succ]
    have hvalI : realizedValue Y.2 i=Y.2 I:=by rw [←hI,realizedValue_succ]
    have hvalJ : realizedValue Y.2 j=Y.2 J:=by rw [←hJ,realizedValue_succ]
    have hYP : Y=(Matrix.gram ℝ x,Y.2):=Prod.ext hgram.symm rfl
    have hdist : Nat.dist I.val J.val≤H:=by
      have he : Nat.dist I.val J.val=Nat.dist i j:=by rw [←hI,←hJ,Nat.dist_add_add_right]
      rwa [he]
    have hh:=hY.2.2 I J hdist
    rw [hYP,pairT_realization,pairR_realization] at hh
    simpa only [datumT,datumR,hposI,hposJ,hgradI,hgradJ,hvalI,hvalJ] using hh
  origin i hi hin:=by
    let I : Fin n:=⟨i-1,by omega⟩
    have hI : (I : ℕ)+1=i:=by dsimp [I]; omega
    have hposI : realizedPosition x i=x I.castSucc.succ:=by rw [←hI]; exact realizedPosition_fin x I.castSucc.succ
    have hgradI : realizedGradient x A B β i=reconstructedGradient x A B β I:=by rw [←hI,realizedGradient_succ]
    have hvalI : realizedValue Y.2 i=Y.2 I:=by rw [←hI,realizedValue_succ]
    have hYP : Y=(Matrix.gram ℝ x,Y.2):=Prod.ext hgram.symm rfl
    have hh:=hY.2.1 I
    rw [hYP,starT_realization,starR_realization] at hh
    simpa only [hposI,hgradI,hvalI] using hh
  recurrence k hk:=by
    let I : Fin n:=⟨k,hk⟩
    have hgrad : realizedGradient x A B β (k+1)=
        (1/B) • (x I.succ.succ-A • x I.castSucc.succ+β • x I.castSucc.castSucc):=by
      rw [show k+1=(I : ℕ)+1 from rfl,realizedGradient_succ]
      exact combination_gradient x A B β I
    have hleft : realizedPosition x k=x I.castSucc.castSucc:=realizedPosition_fin x I.castSucc.castSucc
    have hmid : realizedPosition x (k+1)=x I.castSucc.succ:=realizedPosition_fin x I.castSucc.succ
    have hright : realizedPosition x (k+2)=x I.succ.succ:=realizedPosition_fin x I.succ.succ
    rw [hgrad,hleft,hmid,hright,smul_smul,mul_one_div_cancel hB,one_smul]
    module

/-- The global block records exactly the original position Gram entries and values. -/
theorem segmentOfBlock_window {A B β : ℝ} {H n : ℕ} (hB : B≠0) {Y : WindowSpace n}
    (hY : Y∈blockCone A B β H n) (x : Fin (n+2) → E) (hgram : Matrix.gram ℝ x=Y.1) :
    Matrix.gram ℝ (fun i : Fin (n+2) => (segmentOfBlock hB hY x hgram).x i)=Y.1 ∧
      ∀ i : Fin n,(segmentOfBlock hB hY x hgram).value (i+1)=Y.2 i := by
  constructor
  · simpa only [segmentOfBlock,realizedPosition_fin] using hgram
  · intro i
    exact realizedValue_succ Y.2 i

end polyak.FiniteHorizon
