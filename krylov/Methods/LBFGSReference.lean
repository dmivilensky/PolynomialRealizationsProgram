import krylov.Methods.LBFGS

/-!
Article: main_krylov, cor:lm and s3:cor:qn, genuine BFGS and L-BFGS quadratic execution.
Use: prove the actual full quadratic BFGS/L-BFGS gradients, secant transcript
and global CG consistency from the genuine implemented two-loop update, with
every positive scalar initial metric and newest-retaining positive memory.
Source: exact real line-search scale cancellation, the proved actual two-loop
reference identity and the existing full observed-history execution protocol.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine zero-correction quadratic iteration with an actually scaled CG direction records exactly the true CG gradient and step/secant pair.
Use: Every genuine zero-correction quadratic iteration with an actually scaled CG direction records exactly the true CG gradient and step/secant pair.
Article: main_krylov, cor:lm and s3:cor:qn, genuine BFGS and L-BFGS quadratic execution.
Proof: Reuse true correction-tree invariance and exact-search direction-scale cancellation before identifying the actual new recorded pair. -/
theorem reference_advance_scaled (m : ProbedMethod E) (Q : E →L[ℝ] E) (g : E) (k : ℕ) (H : History E)
    (hg : H.gradient=CG.gradient Q g k) (hp : H.pairs=referencePairs Q g k)
    {c : ℝ} (hc : c≠0) (hd : m.direction H=c • CG.direction Q g k)
    (hz : ZeroCorrections (m.correction H (Q (m.direction H))) Q
      (searchedGradient H.gradient (m.direction H) (Q (m.direction H)))) :
    (methodAdvance m Q Q H).gradient=CG.gradient Q g (k+1) ∧
      (methodAdvance m Q Q H).pairs=referencePairs Q g (k+1) := by
  -- Exact-search scaling is eliminated in both the actual observed gradient and its true recorded physical step.
  have he := (zeroCorrections_change_operator _ Q Q _ hz).2
  have hs : searchedGradient H.gradient (m.direction H) (Q (m.direction H))=CG.gradient Q g (k+1) := by
    rw [hg,hd,map_smul,searchedGradient_smul _ _ _ hc]
    rfl
  constructor
  · change (runCorrections _ Q _).gradient=_
    rw [he.2,hs]
  · change ((lineLength H.gradient (m.direction H) (Q (m.direction H)) • m.direction H+
      (runCorrections _ Q _).movement,
      (runCorrections _ Q _).gradient-H.gradient)::H.pairs)=_
    rw [he.1,he.2,add_zero,hs,hg,hd,map_smul,lineStep_smul _ _ _ hc,hp]
    change (referenceStep Q g k,CG.gradient Q g (k+1)-CG.gradient Q g k)::referencePairs Q g k=_
    rw [CG.gradient_succ,add_sub_cancel_left]
    simp only [referencePairs,referenceStep,map_smul]

/-- The genuine BFGS/L-BFGS decision read from its true reference transcript is its actual positive scalar initialization times the true CG direction.
Use: The genuine BFGS/L-BFGS decision read from its true reference transcript is its actual positive scalar initialization times the true CG direction.
Article: main_krylov, cor:lm and s3:cor:qn, genuine BFGS and L-BFGS quadratic execution.
Proof: Its genuine record count and secant window are determined by the actual transcript; the proved real two-loop reference identity applies. -/
theorem lbfgsMethod_direction (memory : ℕ → ℕ) (scale : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) (H : History E)
    (hg : H.gradient=CG.gradient Q g k) (hp : H.pairs=referencePairs Q g k)
    (hm : CG.gradient Q g k≠0 → 0 < k → 0 < memory k) :
    (lbfgsMethod memory scale).direction H=scale H • CG.direction Q g k := by
  have hl : H.records.length=k := by rw [← H.pairs_length,hp,referencePairs_length]
  change -inverseBFGSApply (scale H) (H.pairs.take (memory H.records.length)) H.gradient=_
  rw [hg,hp,hl]
  exact inverseBFGSApply_reference _ Q hQ hpos g k (memory k) hm

/-- The actual executed BFGS/L-BFGS policy has exactly the genuine quadratic CG gradients and complete step/secant transcript, including solved tails.
Use: The actual executed BFGS/L-BFGS policy has exactly the genuine quadratic CG gradients and complete step/secant transcript, including solved tails.
Article: main_krylov, cor:lm and s3:cor:qn, genuine BFGS and L-BFGS quadratic execution.
Proof: Induct through real histories. The actual retained two-loop direction is a positive CG multiple; genuine exact search cancels that scale and records the true reference pair. -/
theorem lbfgsMethod_static (memory : ℕ → ℕ) (scale : History E → ℝ) (hscale : ∀ H, 0 < scale H)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hm : ∀ k, CG.gradient Q g k≠0 → 0 < k → 0 < memory k) (k : ℕ) :
    let H := methodRun (lbfgsMethod memory scale) (fun _ => Q) (fun _ => Q) g k
    H.gradient=CG.gradient Q g k ∧ H.pairs=referencePairs Q g k := by
  -- The actual transcript invariant is established before the next computed two-loop direction is invoked.
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    exact reference_advance_scaled _ Q g k _ ih.1 ih.2 (hscale _).ne'
      (lbfgsMethod_direction memory scale Q hQ hpos g k _ ih.1 ih.2 (hm k)) trivial

/-- Actual BFGS and every positive newest-retaining L-BFGS method are globally CG-consistent for every genuine positive scalar initialization rule.
Use: Actual BFGS and every positive newest-retaining L-BFGS method are globally CG-consistent for every genuine positive scalar initialization rule.
Article: main_krylov, cor:lm and s3:cor:qn, genuine BFGS and L-BFGS quadratic execution.
Proof: Use the proved true full quadratic transcript and its actual scaled CG direction; the genuine correction tree is empty. -/
theorem lbfgsMethod_consistent (memory : ℕ → ℕ) (hm : ∀ k, 0 < k → 0 < memory k)
    (scale : History E → ℝ) (hscale : ∀ H, 0 < scale H) :
    CGConsistent (lbfgsMethod memory scale) := by
  intro Q hQ hpos g k
  have ht := lbfgsMethod_static memory scale hscale Q hQ hpos g (fun j _ => hm j) k
  exact ⟨_,hscale _,lbfgsMethod_direction memory scale Q hQ hpos g k _ ht.1 ht.2 (fun _ => hm k),trivial⟩
end
end krylov.Methods
