import krylov.Correction.RFCHistoryScaling

/-!
Article: main_krylov, thm:UCg(iii), exact original spectral-decision scaling.
Use: Restore original initial-gradient units in every actual measured gate
while preserving the true retained-history and current-probe coordinates.
Source: proved actual finite observation indexing, exact positive common
model scaling and genuine executed step/secant/direction homogeneity.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine spectral decision of the actual finite observed run passes its original measured test.
Use: Transfer original uniform gated-RFC conclusions without a normalization premise.
Article: main_krylov, thm:UCg(iii).
-/
def actualSpectralGates (m : ProbedMethod E) (memory : ℕ → ℕ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (N : ℕ) (γ : ℝ) : Prop :=
  ∀ k<N, let H := methodRun m A B g k
    let W := selectedWindow memory H
    let d := m.direction H
    spectralGate γ ((d,A k d)::W)

/-- The original actual retained-history spectral decision is exactly its true finite measured step/secant array decision.
Use: Transfer original uniform gated-RFC conclusions without a normalization premise.
Article: main_krylov, thm:UCg(iii).
Proof: The genuine executed-pair dictionary fixes the real retained length and augmented entries. The already proved pure-coordinate spectral test identity transports that same actual model.
-/
theorem actual_spectralGate_iff_array (m : ProbedMethod E) (memory : ℕ → ℕ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (γ : ℝ) :
    let H := methodRun m A B g k
    let d := m.direction H
    spectralGate γ ((d,A k d)::selectedWindow memory H) ↔
      matrixSpectralGate γ (pairModel
        (Fin.cons d (fun i : Fin (min (memory k) k) => probedStep m A B g (k-1-i.val)))
        (Fin.cons (A k d) (fun i : Fin (min (memory k) k) => probedSecant m A B g (k-1-i.val)))) := by
  let H := methodRun m A B g k
  let d := m.direction H
  let s := probedStep m A B g
  let y := probedSecant m A B g
  have hg := augmentedWindow_coordinates s y k (memory k) d (A k d)
  have hgate := spectralGate_coordinates ((d,A k d)::(executedPairs s y k).take (memory k))
    (by simp only [List.length_cons,List.length_take,executedPairs_length])
    (Fin.cons d (fun i : Fin (min (memory k) k) => s (k-1-i.val)))
    (Fin.cons (A k d) (fun i : Fin (min (memory k) k) => y (k-1-i.val))) hg.1 hg.2 γ
  dsimp only
  rw [selectedWindow_methodRun]
  exact hgate

/-- Genuine current-direction and retained measured-pair scaling preserves the exact original spectral decision.
Use: Transfer original uniform gated-RFC conclusions without a normalization premise.
Article: main_krylov, thm:UCg(iii).
Proof: Reindex both real observed windows by the actual finite dictionary. True column, current direction and linear probe identities give a common pair scale; the original measured spectral test is invariant under that scale.
-/
theorem actual_spectralGate_scalar_of_fields (m : ProbedMethod E) (memory : ℕ → ℕ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (γ c : ℝ) (hc : c≠0)
    (hd : m.direction (methodRun m A B (c • g) k)=c • m.direction (methodRun m A B g k))
    (hs : ∀ i<k, probedStep m A B (c • g) i=c • probedStep m A B g i)
    (hy : ∀ i<k, probedSecant m A B (c • g) i=c • probedSecant m A B g i) :
    (let H := methodRun m A B (c • g) k;
      spectralGate γ ((m.direction H,A k (m.direction H))::selectedWindow memory H)) ↔
    (let H := methodRun m A B g k;
      spectralGate γ ((m.direction H,A k (m.direction H))::selectedWindow memory H)) := by
  have hS : (fun j : Fin (min (memory k) k) => probedStep m A B (c • g) (k-1-j.val))=
      fun j => c • probedStep m A B g (k-1-j.val) := by
    funext j
    exact hs _ (by omega)
  have hY : (fun j : Fin (min (memory k) k) => probedSecant m A B (c • g) (k-1-j.val))=
      fun j => c • probedSecant m A B g (k-1-j.val) := by
    funext j
    exact hy _ (by omega)
  have hleft := actual_spectralGate_iff_array m memory A B (c • g) k γ
  have hright := actual_spectralGate_iff_array m memory A B g k γ
  dsimp only at hleft hright ⊢
  rw [hleft,hright,hS,hY,hd,map_smul]
  let S : Fin (min (memory k) k+1) → E :=
    Fin.cons (m.direction (methodRun m A B g k)) (fun j => probedStep m A B g (k-1-j.val))
  let Y : Fin (min (memory k) k+1) → E :=
    Fin.cons (A k (m.direction (methodRun m A B g k))) (fun j => probedSecant m A B g (k-1-j.val))
  have hU : (Fin.cons (c • m.direction (methodRun m A B g k))
      (fun j : Fin (min (memory k) k) => c • probedStep m A B g (k-1-j.val)))=fun j => c • S j := by
    funext j; exact Fin.cases rfl (fun _ => rfl) j
  have hZ : (Fin.cons (c • A k (m.direction (methodRun m A B g k)))
      (fun j : Fin (min (memory k) k) => c • probedSecant m A B g (k-1-j.val)))=fun j => c • Y j := by
    funext j; exact Fin.cases rfl (fun _ => rfl) j
  rw [hU,hZ]
  exact pairSpectralGate_scalar γ S Y c hc

/-- Every actual spectral decision in original gated RFC is invariant under a nonzero common initial-gradient scale.
Use: Transfer original uniform gated-RFC conclusions without a normalization premise.
Article: main_krylov, thm:UCg(iii).
Proof: The proved genuine trajectory field scaling supplies every current direction, retained total step and measured secant identity. Apply exact finite spectral-decision scaling at each real iteration.
-/
theorem gated_actualSpectralGates_scalar (memory : ℕ → ℕ) (γ : ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) (N : ℕ) :
    actualSpectralGates (gatedMethod memory γ) memory A B (c • g) N γ ↔
      actualSpectralGates (gatedMethod memory γ) memory A B g N γ := by
  have hscale := gated_scalar memory γ A B g c hc N
  have hiff k (hk : k<N) := actual_spectralGate_scalar_of_fields (gatedMethod memory γ) memory A B g k γ c hc
    (hscale.2 k hk).1 (fun i hi => (hscale.2 i (hi.trans hk)).2.1)
    (fun i hi => (hscale.2 i (hi.trans hk)).2.2)
  constructor
  · intro h k hk
    exact (hiff k hk).mp (h k hk)
  · intro h k hk
    exact (hiff k hk).mpr (h k hk)

end
end krylov.Correction
