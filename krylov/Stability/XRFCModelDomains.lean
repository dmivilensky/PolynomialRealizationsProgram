import krylov.Stability.ContDiffVirtual

/-!
Article: main_krylov, lem:U(d), genuine full-memory XRFC reference domains.
Use: discharge both actual finite-array inverse domains from the true
executed nonzero-trial quadratic basis invariant, including the final output.
Source: actual XRFC positive model theorem and exact real transcript indexing.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Both true finite-array XRFC inverse matrices are nonsingular throughout the real nonstagnating quadratic prefix and its unevaluated terminal output.
Use: actual C² trajectory regularity has its inverse domains discharged from genuine CG geometry and genuine nonzero trials.
Article: main_krylov, lem:U(d), true secant determinants for XRFC.
Proof: the actual executed XRFC basis theorem makes the real latest model
positive definite. True quadratic images identify the real conjugacy matrix
with that model; exact chronological determinant coordinates transfer this
actual domain to the fixed arrays, whose true pair model is the same matrix. -/
theorem xrfc_full_array_domains (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N, CG.gradient Q g i≠0)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let m := xrfcMethod fullMemory trial (E := E)
    let S := fun i : Fin k => oneGradientStep m (fun _ => Q) g (k-1-i.val)
    let Y := fun i : Fin k => Q (S i)
    (crossGram Y S).det≠0 ∧ (pairModel S Y).det≠0 := by
  -- Derive the true physical inverse domain before transporting any finite matrix coordinates.
  let m := xrfcMethod fullMemory trial (E := E)
  let H := oneGradientRun m (fun _ => Q) g k
  let S := fun i : Fin k => oneGradientStep m (fun _ => Q) g (k-1-i.val)
  let Y := fun i : Fin k => Q (S i)
  have hp := (xrfc_full_model_posDef trial Q hQ hpos g N hpre ht k hk).det_pos.ne'
  have hy : ∀ i, windowImages H.pairs i=Q (windowSteps H.pairs i) := fun i =>
    oneGradientRun_pairs_quadratic m Q g k (H.pairs.get i) (List.get_mem _ i)
  rw [windowModel_quadratic _ Q hQ hy] at hp
  have hY : windowImages H.pairs=fun i => Q (windowSteps H.pairs i) := funext hy
  rw [← hY] at hp
  change (crossGram (windowImages (oneGradientRun m (fun _ => Q) g k).pairs)
    (windowSteps (oneGradientRun m (fun _ => Q) g k).pairs)).det≠0 at hp
  rw [oneGradientRun_pairs_segmentOperators,crossGram_executed_det] at hp
  have hc : (crossGram Y S).det≠0 := hp
  have hm : pairModel S Y=crossGram Y S := by
    change pairModel S (fun i => Q (S i))=crossGram (fun i => Q (S i)) S
    rw [pairModel_quadratic S Q hQ]
    ext i j
    exact (hQ (S i) (S j)).symm
  exact ⟨hc,by rw [hm]; exact hc⟩

end
end krylov.Stability
