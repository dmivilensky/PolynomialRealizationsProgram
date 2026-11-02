import krylov.Information.TwinReplay

/-!
Article: main_krylov, thm:centre, the actual information fibre and its data-only centre.
Use: recover every earlier direction and probe from an equal complete history,
and show that the physical latest-information model is constant on that fibre.
Source: the actual iteration record, genuine chronological execution and the
existing physical secant-pair model. No extra observations are added to the fibre.
-/

namespace krylov.Information
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.LinearAlgebra krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Remove the latest actual iteration record, retaining the initial observed gradient.
Use: recover every shorter true history from a longer complete observed history.
Article: main_krylov, def:classes(M), recoverable past data. -/
def previousHistory (H : History E) : History E := ⟨H.initial,H.records.tail⟩

/-- Removing the latest record of a genuine successor run recovers its actual preceding history.
Use: equality of complete histories forces equality at every earlier time.
Article: main_krylov, thm:centre, preservation of all prefix observations.
Proof: the actual iteration executor prepends exactly its new record. -/
theorem previousHistory_run (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E)
    (g : E) (k : ℕ) : previousHistory (methodRun m A B g (k+1))=methodRun m A B g k := rfl

/-- Equal complete histories force equal histories at every earlier actual time.
Use: the original information fibre already contains every old direction and old probe.
Article: main_krylov, thm:centre, prefix information in the actual data fibre.
Proof: repeatedly remove the latest real record until the specified prefix
is reached; no relation between the unobserved operators is assumed. -/
theorem run_prefix_eq (m : ProbedMethod E) (A B C D : ℕ → E →L[ℝ] E) (g : E)
    {N : ℕ} (heq : methodRun m A B g N=methodRun m C D g N) {k : ℕ} (hk : k≤N) :
    methodRun m A B g k=methodRun m C D g k := by
  -- Removing a real record preserves equality independently of both unobserved oracle sequences.
  induction N with
  | zero =>
    have h : k=0 := by omega
    subst k
    rfl
  | succ N ih =>
    by_cases h : k=N+1
    · subst k
      exact heq
    · exact ih (congrArg previousHistory heq) (by omega)

/-- The latest actual probe stored in a history, with zero only for an empty past.
Use: extract genuine old search observations from equality of complete records.
Article: main_krylov, def:classes(M), observed z_k. -/
def latestRecordedProbe (H : History E) : E :=
  match H.records with | [] => 0 | r::_ => r.probe

/-- The latest recorded probe of a genuine successor run is precisely its actual preceding probe.
Use: translate observed-history equality into actual oracle-action equality.
Article: main_krylov, thm:centre, old probes determined by data.
Proof: the actual next iteration record stores the actual current search image. -/
theorem latestRecordedProbe_run (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E)
    (g : E) (k : ℕ) : latestRecordedProbe (methodRun m A B g (k+1))=probedProbe m A B g k := rfl

/-- An equal complete past determines each earlier actual probe without an additional fibre constraint.
Use: prove that the information centre truly depends only on the allowed data.
Article: main_krylov, thm:centre, data-only latest-information model.
Proof: extract the latest probe from the equal successor prefix histories. -/
theorem probe_eq_of_run_eq (m : ProbedMethod E) (A B C D : ℕ → E →L[ℝ] E) (g : E)
    {N : ℕ} (heq : methodRun m A B g N=methodRun m C D g N) {k : ℕ} (hk : k<N) :
    probedProbe m A B g k=probedProbe m C D g k :=
  congrArg latestRecordedProbe (run_prefix_eq m A B C D g heq (by omega : k+1≤N))

variable {p : ℕ}

/-- The exact allowed information fibre before the final correction decision.
Use: admissibility and information equality remain separate constraints.
Article: main_krylov, thm:centre, complete preterminal data and final search probe. -/
def Scenario.observationFibre (m : ProbedMethod (EuclideanSpace ℝ (Fin p)))
    (g : EuclideanSpace ℝ (Fin p)) (N : ℕ) (H : History (EuclideanSpace ℝ (Fin p)))
    (z : EuclideanSpace ℝ (Fin p)) : Set (Scenario p) :=
  {S | methodRun m S.probeOracle (S.correctionOracle N) g N=H ∧
    probedProbe m S.probeOracle (S.correctionOracle N) g N=z}

/-- The genuine admissible information fibre in the original base ball and finite profile.
Use: the centre radius below takes its supremum over real admissible scenarios.
Article: main_krylov, thm:centre, admissible fibre 𝒮∩𝒟. -/
def Scenario.admissibleFibre (m : ProbedMethod (EuclideanSpace ℝ (Fin p)))
    (g : EuclideanSpace ℝ (Fin p)) (N : ℕ) (H : History (EuclideanSpace ℝ (Fin p)))
    (z : EuclideanSpace ℝ (Fin p)) (A : Matrix (Fin p) (Fin p) ℝ)
    (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) : Set (Scenario p) :=
  {S | S.Admissible N A r ω w τ ∧ S∈Scenario.observationFibre m g N H z}

/-- Every scenario in the same actual information fibre has the same own direction matrix.
Use: one nondegenerate actual direction basis defines the common fibre geometry.
Article: main_krylov, thm:centre, direction flag determined by data.
Proof: equal full histories give equal histories before every direction
decision, including the last one; the policy is genuinely nonanticipating. -/
theorem Scenario.direction_fibre {N : ℕ} (O T : Scenario (N+1))
    (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (g : EuclideanSpace ℝ (Fin (N+1)))
    (hh : methodRun m O.probeOracle (O.correctionOracle N) g N=
      methodRun m T.probeOracle (T.correctionOracle N) g N)
    (hdir : ∀ i : Fin (N+1), probedDirection m O.probeOracle (O.correctionOracle N) g i.val=
      euclideanColumn D i) (i : Fin (N+1)) :
    probedDirection m T.probeOracle (T.correctionOracle N) g i.val=euclideanColumn D i := by
  have hp := run_prefix_eq m O.probeOracle (O.correctionOracle N) T.probeOracle
    (T.correctionOracle N) g hh (by omega : i.val≤N)
  change m.direction (methodRun m _ _ g i.val)=_
  rw [← hp]
  exact hdir i

/-- Equal actual information determines every measured physical direction/probe column.
Use: the data fibre contains precisely the observations used by the centre.
Article: main_krylov, thm:centre, the measured matrix is constant on the fibre.
Proof: recover each earlier actual probe from its recorded successor history;
use the given common last probe for the final column, and the common actual
direction basis for both physical matrix actions. -/
theorem Scenario.pairImages_fibre {N : ℕ} (O T : Scenario (N+1))
    (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (g : EuclideanSpace ℝ (Fin (N+1)))
    (hh : methodRun m O.probeOracle (O.correctionOracle N) g N=
      methodRun m T.probeOracle (T.correctionOracle N) g N)
    (hz : probedProbe m O.probeOracle (O.correctionOracle N) g N=
      probedProbe m T.probeOracle (T.correctionOracle N) g N)
    (hdir : ∀ i : Fin (N+1), probedDirection m O.probeOracle (O.correctionOracle N) g i.val=
      euclideanColumn D i) : pairImages D O.probe=pairImages D T.probe := by
  -- The current probe is supplied once; all previous probe columns are recovered from real records.
  ext a i
  have hp : probedProbe m O.probeOracle (O.correctionOracle N) g i.val=
      probedProbe m T.probeOracle (T.correctionOracle N) g i.val := by
    by_cases hi : i.val=N
    · simpa only [hi] using hz
    · exact probe_eq_of_run_eq m _ _ _ _ g hh (by omega)
  change O.probeOracle i.val (probedDirection m _ _ g i.val)=
    T.probeOracle i.val (probedDirection m _ _ g i.val) at hp
  rw [hdir i,O.direction_fibre T D m g hh hdir i] at hp
  exact congrArg (fun v : EuclideanSpace ℝ (Fin (N+1)) => v a) hp

/-- The actual physical latest-information centre is identical on the exact allowed data fibre.
Use: its minimax comparison is against one data-only matrix common to the entire fibre.
Article: main_krylov, thm:centre(v), J_D determined by data.
Proof: the two genuine measured pair matrices agree by the proved history
recovery; the same inverse direction congruence reconstructs their centres. -/
theorem Scenario.physicalCentre_fibre {N : ℕ} (S T : Scenario (N+1))
    (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (g : EuclideanSpace ℝ (Fin (N+1)))
    (hh : methodRun m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N=
      methodRun m (T.inPhysical D).probeOracle ((T.inPhysical D).correctionOracle N) g N)
    (hz : probedProbe m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N=
      probedProbe m (T.inPhysical D).probeOracle ((T.inPhysical D).correctionOracle N) g N)
    (hdir : ∀ i : Fin (N+1), probedDirection m (S.inPhysical D).probeOracle
      ((S.inPhysical D).correctionOracle N) g i.val=euclideanColumn D i) :
    S.physicalCentre D=T.physicalCentre D := by
  exact congrArg (fun Y => inverseFormMap D (latest (Dᵀ*Y)))
    ((S.inPhysical D).pairImages_fibre (T.inPhysical D) D m g hh hz hdir)

/-- The completed twin has the same final probe after its preserved complete past.
Use: the admissible completed twin belongs to the original allowed information fibre.
Article: main_krylov, thm:centre(iii), final data after H4 replacement.
Proof: equal actual histories choose the same last direction; correction
completion leaves the reflected last probe column exactly fixed. -/
theorem Scenario.completed_twin_probe {N : ℕ} (S T : Scenario (N+1))
    (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hD : IsUnit D.det)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (g : EuclideanSpace ℝ (Fin (N+1)))
    (hh : methodRun m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N=
      methodRun m T.probeOracle (T.correctionOracle N) g N)
    (hp : T.probe N=((S.reflect N).inPhysical D).probe N)
    (hdir : ∀ i : Fin (N+1), probedDirection m (S.inPhysical D).probeOracle
      ((S.inPhysical D).correctionOracle N) g i.val=euclideanColumn D i) :
    probedProbe m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N=
      probedProbe m T.probeOracle (T.correctionOracle N) g N := by
  -- Identify the true last chosen direction before using the fixed reflected physical column.
  change (S.inPhysical D).probeOracle N (m.direction (methodRun m _ _ g N))=
    T.probeOracle N (m.direction (methodRun m _ _ g N))
  rw [← hh]
  change (S.inPhysical D).probeOracle N (probedDirection m _ _ g N)=
    T.probeOracle N (probedDirection m _ _ g N)
  have hd := hdir (Fin.last N)
  simp only [Fin.val_last] at hd
  rw [hd]
  change cgOperator ((S.inPhysical D).probe N) (euclideanColumn D (Fin.last N))=
    cgOperator (T.probe N) (euclideanColumn D (Fin.last N))
  rw [hp]
  ext a
  exact (S.physical_reflect_probe_column D hD le_rfl (Fin.last N) rfl a).symm

end
end krylov.Information
