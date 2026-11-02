import krylov.Methods.HistoryShape

/-!
Article: main_krylov, def:classes and lem:U(d), genuine local finite-policy bridges.
Use: transfer the proved real compiled-program regularity to actual raw
policies whose primitive decisions agree on a true observed-data neighborhood,
including locally fixed optional correction branches and correction counts.
Source: actual finite observation charts, real oracle-probe continuity and
complete-history nonanticipating execution; no actual cycle expansion is assumed.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A genuine decision property holds on a neighborhood of the true finite observed history and actual probe.
Use: A genuine decision property holds on a neighborhood of the true finite observed history and actual probe.
Article: main_krylov, def:classes and lem:U(d), genuine local finite-policy bridges.
Proof: Every finite-vector presentation uses the true fixed iteration and correction-query shape together with its actual observation topology. -/
def ObservedLocalAt (H₀ : History E) (z₀ : E) (predicate : History E → E → Prop) : Prop :=
  ∀ (n : ℕ) (data : Fin n → E), H₀.observationList=List.ofFn data →
    ∃ V : Set ((Fin n → E) × E), V∈𝓝 (data,z₀) ∧
      ∀ q∈V, ∀ H : History E, H.queryShape=H₀.queryShape →
        H.observationList=List.ofFn q.1 → predicate H q.2

/-- A raw policy and a primitive compiled policy make the same actual decisions on a genuine local observed-data branch.
Use: A raw policy and a primitive compiled policy make the same actual decisions on a genuine local observed-data branch.
Article: main_krylov, def:classes and lem:U(d), genuine local finite-policy bridges.
Proof: The condition concerns only the true direction and correction-tree decisions at observed data, without a trajectory regularity premise. -/
def LocalCompiledAt (m : ProbedMethod E) (P : CompiledProbedPolicy E) (H : History E) (z : E) : Prop :=
  ObservedLocalAt H z (fun H' z' => m.direction H'=P.method.direction H' ∧
    m.correction H' z'=P.method.correction H' z')

/-- A true local observed-data decision property holds along genuine smooth finite histories and their actual continuous probes.
Use: A true local observed-data decision property holds along genuine smooth finite histories and their actual continuous probes.
Article: main_krylov, def:classes and lem:U(d), genuine local finite-policy bridges.
Proof: Compose the actual finite-vector chart with the real probe; its true reference neighborhood is reached eventually. -/
theorem observedLocal_eventually (H : X → History E) (z : X → E) (x : X) {r : WithTop ℕ∞}
    (hH : SmoothListAt r (fun p => (H p).observationList) x) (hz : ContinuousAt z x)
    (hshape : ∀ᶠ p in 𝓝 x, (H p).queryShape=(H x).queryShape)
    (predicate : History E → E → Prop) (hlocal : ObservedLocalAt (H x) (z x) predicate) :
    ∀ᶠ p in 𝓝 x, predicate (H p) (z p) := by
  -- The true local branch is tested in actual observed-vector coordinates.
  obtain ⟨n,data,hd,he⟩ := hH
  obtain ⟨V,hV,hmatch⟩ := hlocal n (data x) he.self_of_nhds
  have hp := (hd.continuousAt.prodMk hz).tendsto.eventually hV
  filter_upwards [he,hp,hshape] with p hobs hmem hs
  exact hmatch (data p,z p) hmem (H p) hs hobs

/-- A raw locally compiled probed method and the primitive compiled executor have identical actual complete histories on a genuine parameter neighborhood.
Use: A raw locally compiled probed method and the primitive compiled executor have identical actual complete histories on a genuine parameter neighborhood.
Article: main_krylov, def:classes and lem:U(d), genuine local finite-policy bridges.
Proof: Induct over actual queries. The compiled real history is smooth, so the true local observed-data branch persists; equal actual preceding histories and identical real direction/correction decisions give identical next records. -/
theorem localCompiled_methodRun (m : ProbedMethod E) (P : CompiledProbedPolicy E)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ) {r : WithTop ℕ∞}
    (hA : ∀ k<N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ k<N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ContDiffAt ℝ r g x)
    (hcoef : ∀ k<N, P.CoefficientsRegularAt r (methodRun P.method (A x) (B x) (g x) k) (A x k) (B x k))
    (hcurv : ∀ k<N, inner ℝ (P.method.direction (methodRun P.method (A x) (B x) (g x) k))
      (A x k (P.method.direction (methodRun P.method (A x) (B x) (g x) k)))≠0)
    (hlocal : ∀ k<N, LocalCompiledAt m P (methodRun P.method (A x) (B x) (g x) k)
      (A x k (P.method.direction (methodRun P.method (A x) (B x) (g x) k)))) :
    ∀ᶠ p in 𝓝 x, methodRun m (A p) (B p) (g p) N=methodRun P.method (A p) (B p) (g p) N := by
  -- Equal actual preceding histories force equal real decisions and complete next records.
  induction N with
  | zero => exact Eventually.of_forall fun _ => rfl
  | succ k ih =>
    have heq := ih (fun j hj => hA j (by omega)) (fun j hj => hB j (by omega))
      (fun j hj => hcoef j (by omega)) (fun j hj => hcurv j (by omega)) (fun j hj => hlocal j (by omega))
    have htrace := P.run_regular A B g x k (fun j hj => hA j (by omega)) (fun j hj => hB j (by omega)) hg
      (fun j hj => hcoef j (by omega)) (fun j hj => hcurv j (by omega))
    have hd := listDecision_contDiffAt P.directionRule _ x htrace (hcoef k (by omega)).1
    have hz := (hA k (by omega)).clm_apply hd
    have hshape : ∀ᶠ p in 𝓝 x,
        (methodRun P.method (A p) (B p) (g p) k).queryShape=
          (methodRun P.method (A x) (B x) (g x) k).queryShape :=
      Filter.Eventually.of_forall fun p => P.run_queryShape (A p) (B p) (A x) (B x) (g p) (g x) k
    have hmatch := observedLocal_eventually _ _ x htrace hz.continuousAt hshape _ (hlocal k (by omega))
    filter_upwards [heq,hmatch] with p hp hpol
    let H₁ := methodRun P.method (A p) (B p) (g p) k
    have hc : m.correction H₁ (A p k (P.method.direction H₁))=
        P.method.correction H₁ (A p k (P.method.direction H₁)) := hpol.2
    rw [methodRun,methodRun,hp]
    dsimp only [methodAdvance]
    rw [hpol.1,hc]

/-- A genuinely locally compiled raw method inherits actual returned-gradient C-r regularity from its real compiled finite history.
Use: A genuinely locally compiled raw method inherits actual returned-gradient C-r regularity from its real compiled finite history.
Article: main_krylov, def:classes and lem:U(d), genuine local finite-policy bridges.
Proof: Transfer the genuine local complete-history equality to the true returned-gradient coordinate. -/
theorem localCompiled_gradient_regular (m : ProbedMethod E) (P : CompiledProbedPolicy E)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ) {r : WithTop ℕ∞}
    (htrace : SmoothListAt r (fun p => (methodRun P.method (A p) (B p) (g p) N).observationList) x)
    (heq : ∀ᶠ p in 𝓝 x, methodRun m (A p) (B p) (g p) N=methodRun P.method (A p) (B p) (g p) N) :
    ContDiffAt ℝ r (fun p => (methodRun m (A p) (B p) (g p) N).gradient) x := by
  apply (P.gradient_regular A B g x N htrace).congr_of_eventuallyEq
  exact heq.mono fun p hp => congrArg History.gradient hp
end
end krylov.Methods
