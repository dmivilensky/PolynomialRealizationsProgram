import krylov.Methods.Protocol

/-!
Article: main_krylov, lem:terminal-fibre, actual quadratic reference comparison.
Use: connect global CG consistency to actual executed histories and the
concrete reference recurrence, allowing every permitted positive direction scale.
Source: exact-search scaling invariance and the proved nonanticipating protocol induction.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual static run of a CG-consistent method has the actual concrete CG gradient.
Use: consistency of directions and zero corrections produces the true reference trajectory.
Article: main_krylov, lem:terminal-fibre, reference gradients.
Proof: induct through the actual run; its zero correction tree leaves the actual
post-search gradient unchanged, and exact-search scaling cancels the allowed positive direction factor. -/
theorem quadratic_gradient_eq_cg (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    (methodRun m (fun _ => Q) (fun _ => Q) g k).gradient=(cgRun Q g k).gradient := by
  -- Zero correction queries preserve the true post-search gradient at each actual reference iteration.
  induction k with
  | zero => rfl
  | succ k ih =>
    let H := methodRun m (fun _ => Q) (fun _ => Q) g k
    obtain ⟨scale, hs, hd, hz⟩ := hm Q hQ hpos g k
    have he := (zeroCorrections_change_operator _ Q Q _ hz).2.2
    change (runCorrections (m.correction H (Q (m.direction H))) Q
      (searchedGradient H.gradient (m.direction H) (Q (m.direction H)))).gradient = _
    rw [he]
    change searchedGradient H.gradient (m.direction H) (Q (m.direction H))=
      searchedGradient (cgRun Q g k).gradient (cgRun Q g k).direction (Q (cgRun Q g k).direction)
    rw [hd, map_smul, ih, searchedGradient_smul _ _ _ hs.ne']

/-- Actual matching CG probes force the entire actual method prefix to equal its quadratic reference.
Use: proves the information-theoretic quantification over all nonanticipating CG-consistent policies.
Article: main_krylov, lem:terminal-fibre, all data through the penultimate search.
Proof: consistency supplies a true positive CG direction scale and an actual zero
correction tree on each static history; linearity transports matching true reference
probes to that scaled direction, and the proved full-history shadow induction applies. -/
theorem cgConsistent_shadow (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (A B : ℕ → E →L[ℝ] E) (g : E) (N : ℕ)
    (hprobe : ∀ k<N, A k (cgRun Q g k).direction=Q (cgRun Q g k).direction) :
    ∀ k≤N, methodRun m A B g k=methodRun m (fun _ => Q) (fun _ => Q) g k := by
  apply methodRun_shadow
  intro k hk
  obtain ⟨scale, hs, hd, hz⟩ := hm Q hQ hpos g k
  refine ⟨?_, hz⟩
  rw [hd, map_smul, map_smul, hprobe k hk]

/-- Concrete nonanticipating CG policy, using only previously observed gradients and directions.
Use: supplies a genuine member of the quantified CG-consistent method class.
Article: main_krylov, def:classes(M), nonanticipating CG without corrections.
Source: standard Fletcher--Reeves recurrence. -/
def cgMethod : ProbedMethod E where
  direction H := match H.records with
    | [] => -H.initial
    | r::rs => -r.gradient+(‖r.gradient‖^2/‖(History.mk H.initial rs).gradient‖^2) • r.direction
  correction _ _ := .done

/-- A concrete nonanticipating CG policy produces exactly the true quadratic CG gradient and direction.
Use: verifies that the quantified policy consistency predicate has a real implementation.
Article: main_krylov, def:classes(M) and lem:terminal-fibre, genuine reference policy.
Proof: induct on the actual executed history; its zero correction tree and
explicit newest-record direction formula are exactly the concrete CG update. -/
theorem cgMethod_static (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    let H := methodRun (cgMethod : ProbedMethod E) (fun _ => Q) (fun _ => Q) g k
    H.gradient=(cgRun Q g k).gradient ∧ cgMethod.direction H=(cgRun Q g k).direction := by
  -- Keep the actual previous history intact so its observed gradient and direction match the induction hypotheses.
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    let H := methodRun (cgMethod : ProbedMethod E) (fun _ => Q) (fun _ => Q) g k
    have hg : H.gradient=(cgRun Q g k).gradient := ih.1
    have hd : cgMethod.direction H=(cgRun Q g k).direction := ih.2
    constructor
    · change searchedGradient H.gradient (cgMethod.direction H) (Q (cgMethod.direction H))=
        (cgAdvance Q (cgRun Q g k)).gradient
      rw [hg, hd]
      rfl
    · change -searchedGradient H.gradient (cgMethod.direction H) (Q (cgMethod.direction H))+
        (‖searchedGradient H.gradient (cgMethod.direction H) (Q (cgMethod.direction H))‖^2/‖H.gradient‖^2) •
          cgMethod.direction H=(cgAdvance Q (cgRun Q g k)).direction
      rw [hg, hd]
      rfl

/-- Concrete nonanticipating CG is genuinely globally CG-consistent on every positive quadratic.
Use: the method class used in the data-fibre lower bound is nonempty without any assumed trajectory witness.
Article: main_krylov, def:classes(M), CG consistency.
Proof: its actual static run is the actual reference recurrence, with scale one
and an actually empty correction decision tree. -/
theorem cgMethod_consistent : CGConsistent (cgMethod : ProbedMethod E) := by
  intro Q _ _ g k
  refine ⟨1, zero_lt_one, ?_, trivial⟩
  simpa only [one_smul] using (cgMethod_static Q g k).2

end
end krylov.Methods
