import krylov.Stability.ContDiffVirtual
import krylov.Methods.EvaluatedLaunch

/-!
Article: main_krylov, prop:EL, genuine evaluated-launch inverse domains.
Use: derive every real virtual solve domain from the actual conjugate basis
on a full nonzero-trial quadratic reference.
Source: true quadratic recorded images and positive operator Gram matrices.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Both actual finite virtual inverse domains hold for the genuine
evaluated-launch reference prefix and its output. Article: prop:EL. -/
theorem evaluatedLaunch_array_domains (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N, CG.gradient Q g i≠0)
    (ht : ∀ i<N, trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g i)≠0)
    (k : ℕ) (hk : k≤N) :
    let m := evaluatedLaunchMethod trial (E := E)
    let S := fun i : Fin k => oneGradientStep m (fun _ => Q) g (k-1-i.val)
    let Y := fun i : Fin k => Q (S i)
    (crossGram Y S).det≠0 ∧ (pairModel S Y).det≠0 := by
  -- Derive the true physical inverse domain before transporting any finite matrix coordinates.
  let m := evaluatedLaunchMethod trial (E := E)
  let H := oneGradientRun m (fun _ => Q) g k
  let S := fun i : Fin k => oneGradientStep m (fun _ => Q) g (k-1-i.val)
  let Y := fun i : Fin k => Q (S i)
  have hpd : (windowModel H.pairs).PosDef := by
    have hy : ∀ i,windowImages H.pairs i=Q (windowSteps H.pairs i) := fun i=>
      oneGradientRun_pairs_quadratic m Q g k (H.pairs.get i) (List.get_mem _ i)
    rw [windowModel_quadratic H.pairs Q hQ hy]
    exact operatorGram_posDef Q hQ hpos (evaluated_launch_basis trial Q hQ hpos g N hpre ht k hk).1
  have hp := hpd.det_pos.ne'
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
end krylov.Convergence
