import krylov.Stability.ContDiffXRFC
import krylov.Methods.HomogeneousXRFC
import krylov.Stability.CompactSmooth
import krylov.Stability.HomogeneousTaylor

/-!
Article: main_krylov, lem:U(a,c,d), true compact-reference XRFC outputs.
Use: apply the complete real C^r execution theorem to actual unevaluated
physical points and semantic gradients, with genuine homogeneous-cone transfer.
Source: primitive observed trial-chart smoothness, proved actual quadratic
inverse domains, real trajectory homogeneity and the compact integral Taylor theorem.
-/

namespace krylov.Stability
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- The genuine unevaluated physical XRFC output paired with its true semantic output gradient.
Use: one real finite output tuple gives simultaneous compact Taylor estimates for both actual vector outputs.
Article: main_krylov, lem:U(a,d), actual XRFC output map. -/
def xrfcOutputPair (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (B : E →L[ℝ] E)
    (g : E) (N : ℕ) : E × E :=
  let m := xrfcMethod fullMemory trial
  let H := oneGradientRun m A g N
  (m.outputDisplacement H,m.outputGradient B H)

omit [CompleteSpace E] [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] in
/-- The genuine XRFC point/gradient output tuple is positively homogeneous under primitive degree-zero observed trials.
Use: actual compact output Taylor constants extend to the full positive cone.
Article: main_krylov, lem:U(c,d).
Proof: both real vector outputs have the proved actual one-gradient execution homogeneity. -/
theorem xrfcOutputPair_scalar (trial : History E → ℝ) (ht : ObservedTrialHomogeneous trial)
    (A : ℕ → E →L[ℝ] E) (B : E →L[ℝ] E) (g : E) (N : ℕ) (c : ℝ) (hc : 0<c) :
    xrfcOutputPair trial A B (c • g) N=c • xrfcOutputPair trial A B g N := by
  have hp := xrfc_scalar_output trial ht A B g c hc N
  exact Prod.ext hp.1 hp.2

/-- Actual XRFC output points and semantic gradients have one genuine compact weighted Taylor radius and constant under primitive C^r observed-data trials.
Use: r=2 is the source's actual compact-uniform XRFC specialization, without an analytic trial assumption or supplied trajectory regularity.
Article: main_krylov, lem:U(a,d).
Proof: actual quadratic execution positivity discharges every inverse domain;
real C^r primitive trial charts give the actual C^r point and gradient outputs.
Apply the genuine finite-order compact weighted Taylor theorem to their true pair. -/
theorem quadraticXRFC_compact_weighted_taylor (trial : History E → ℝ)
    (A : X → ℕ → E →L[ℝ] E) (B : X → E →L[ℝ] E) (g : X → E)
    (e : X → ℝ) (N r : ℕ) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K, ∀ i, ContDiffAt ℝ r (fun z => A z i) x)
    (hB : ∀ x∈K, ContDiffAt ℝ r B x) (hg : ∀ x∈K, ContDiffAt ℝ r g x)
    (hquad : ∀ x∈K, ∃ Q : E →L[ℝ] E, A x=(fun _ => Q) ∧ Q.toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) ∧ (∀ i<N, CG.gradient Q (g x) i≠0) ∧
      ∀ i<N, trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) (g x) i)≠0)
    (hT : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A x) (g x) k))
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    let Φ := fun z => xrfcOutputPair trial (A z) (B z) (g z) N
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖Φ (x+h)-taylorPolynomial Φ k x h‖≤C*‖h‖^k*e x := by
  -- The paired real outputs share one radius and constant because their actual product map is genuinely C^r.
  dsimp only
  apply compact_smooth_weighted_taylor (fun z => xrfcOutputPair trial (A z) (B z) (g z) N) e r K hK _ he hepos
  intro x hx
  obtain ⟨Q,hAx,hQ,hpos,hpre,ht⟩ := hquad x hx
  have hp := quadraticXRFC_output_contDiffAt trial A B g x (hA x hx) (hB x hx) (hg x hx)
    Q hAx hQ hpos N hpre ht (hT x hx)
  exact hp.1.prodMk hp.2

/-- Actual full-memory XRFC point and gradient output Taylor bounds have exactly the same constants on the full positive reference cone under primitive degree-zero C^r trials.
Use: r=2 completes the actual homogeneous compact-cone remainder for the source's C² XRFC trial rule.
Article: main_krylov, lem:U(c,d).
Proof: genuine primitive trial smoothness gives the actual compact weighted
output bound. The real execution homogeneity scales the actual paired output
and its true finite Taylor polynomial by the same positive factor, preserving
the common radius and constant on every positive initial-gradient scale. -/
theorem quadraticXRFC_compact_cone_taylor (trial : History E → ℝ)
    (hHom : ObservedTrialHomogeneous trial)
    (A : X → ℕ → E →L[ℝ] E) (B : X → E →L[ℝ] E) (g : X → E)
    (e : X → ℝ) (N r : ℕ) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K, ∀ i, ContDiffAt ℝ r (fun z => A z i) x)
    (hB : ∀ x∈K, ContDiffAt ℝ r B x) (hg : ∀ x∈K, ContDiffAt ℝ r g x)
    (hquad : ∀ x∈K, ∃ Q : E →L[ℝ] E, A x=(fun _ => Q) ∧ Q.toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) ∧ (∀ i<N, CG.gradient Q (g x) i≠0) ∧
      ∀ i<N, trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) (g x) i)≠0)
    (hT : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A x) (g x) k))
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ∀ c : ℝ, 0<c →
      let Φc := fun z => xrfcOutputPair trial (A z) (B z) (c • g z) N
      ‖Φc (x+h)-taylorPolynomial Φc k x h‖≤C*‖h‖^k*(c*e x) := by
  -- Introduce the scale only after obtaining the common genuine compact output estimate.
  obtain ⟨δ,C,hδ,hC,hrem⟩ := quadraticXRFC_compact_weighted_taylor trial A B g e N r K hK hA hB hg hquad hT he hepos
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx h hh k hk hkr c hc
  let Φ := fun z => xrfcOutputPair trial (A z) (B z) (g z) N
  have hΦ : ContDiffAt ℝ k Φ x := by
    obtain ⟨Q,hAx,hQ,hpos,hpre,ht⟩ := hquad x hx
    have hp := quadraticXRFC_output_contDiffAt trial A B g x (hA x hx) (hB x hx) (hg x hx)
      Q hAx hQ hpos N hpre ht (hT x hx)
    exact (hp.1.prodMk hp.2).of_le (by exact_mod_cast hkr)
  have heq : (fun z => xrfcOutputPair trial (A z) (B z) (c • g z) N)=fun z => c • Φ z :=
    funext fun z => xrfcOutputPair_scalar trial hHom (A z) (B z) (g z) N c hc
  dsimp only
  rw [heq,taylorPolynomial_const_smul Φ k x h c hΦ,
    xrfcOutputPair_scalar trial hHom (A (x+h)) (B (x+h)) (g (x+h)) N c hc,
    ← smul_sub,norm_smul,Real.norm_of_nonneg hc.le]
  exact (mul_le_mul_of_nonneg_left (hrem x hx h hh k hk hkr) hc.le).trans_eq (by ring)

end
end krylov.Stability
