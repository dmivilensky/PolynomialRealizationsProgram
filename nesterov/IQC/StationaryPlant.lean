import nesterov.IQC.Observation
import nesterov.IQC.StationaryResponse
import nesterov.IQC.LinearFilters

/-!
The actual stable strictly causal query plant. It is constructed from the full
normalized recurrence; its zero-state latent output satisfies p(D)w=σ exactly,
and its observed output satisfies q=u(D)w. No common mode is removed.
-/
namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
open nesterov.IQC polyak.General.IQC polyak.Energy
variable (M : nesterov.StationaryMethod)

def firstIndex : Fin M.memory:=⟨0,M.memory_pos⟩

/-- Stable causal impulse from normalized gradients to the original queries. -/
def queryImpulse (μ L t : ℝ) : ℕ→ℝ :=
  observationImpulse (M.realTransitionCoeff μ L t) (M.discountedQueryCoeff t)
    (M.inputScale μ L t) M.lastIndex

/-- Stable causal impulse from normalized gradients to latent iterates. -/
def latentImpulse (μ L t : ℝ) : ℕ→ℝ :=
  stateImpulse (M.realTransitionCoeff μ L t) (M.inputScale μ L t) M.firstIndex M.lastIndex

@[simp] theorem queryImpulse_zero (μ L t : ℝ) : M.queryImpulse μ L t 0=0:=
  observationImpulse_zero _ _ _ _

@[simp] theorem latentImpulse_zero (μ L t : ℝ) : M.latentImpulse μ L t 0=0:=rfl

theorem realTransition_powers_summable {μ L t : ℝ} (hμL : μ<L)
    (hstable : ∀ z : ℂ,((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 →
      ‖z‖<Real.exp t) :
    Summable (fun n : ℕ=>‖companion M.memory (fun j=>(M.realTransitionCoeff μ L t j:ℂ))^n‖) := by
  simpa only [M.coe_realTransitionCoeff] using M.transition_powers_summable hμL hstable

theorem queryImpulse_summable {μ L t : ℝ} (hμL : μ<L)
    (hstable : ∀ z : ℂ,((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 →
      ‖z‖<Real.exp t) : Summable (fun n=>|M.queryImpulse μ L t n|) :=
  observationImpulse_summable _ _ _ _ (M.realTransition_powers_summable hμL hstable)

theorem latentImpulse_summable {μ L t : ℝ} (hμL : μ<L)
    (hstable : ∀ z : ℂ,((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 →
      ‖z‖<Real.exp t) : Summable (fun n=>|M.latentImpulse μ L t n|) :=
  stateImpulse_summable _ _ _ _ (M.realTransition_powers_summable hμL hstable)

section Vector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual latent zero-state causal response. -/
def zeroLatent (μ L t : ℝ) (input : ℕ→E) (k : ℕ) : E :=
  forcedState (M.realTransitionCoeff μ L t) (M.inputScale μ L t) M.lastIndex input k M.firstIndex

theorem zeroLatent_convolution (μ L t : ℝ) (input : ℕ→E) (k : ℕ) :
    M.zeroLatent μ L t input k=convolution (M.latentImpulse μ L t) input k:=
  forcedState_convolution _ _ _ _ _ _

@[simp] theorem zeroLatent_initial (μ L t : ℝ) (input : ℕ→E) (j : Fin M.memory) :
    M.zeroLatent μ L t input j.val=0 :=
  forcedState_initial M.memory_pos _ _ input j

theorem zeroLatent_state (μ L t : ℝ) (input : ℕ→E) (k : ℕ) (j : Fin M.memory) :
    M.zeroLatent μ L t input (k+j.val)=
      forcedState (M.realTransitionCoeff μ L t) (M.inputScale μ L t) M.lastIndex input k j :=
  (forcedState_shift M.memory_pos _ _ input k j).symm

/-- Its observed query is the literal strictly causal convolution. -/
theorem zeroLatent_query (μ L t : ℝ) (input : ℕ→E) (k : ℕ) :
    (∑ j,M.discountedQueryCoeff t j • M.zeroLatent μ L t input (k+j.val))=
      convolution (M.queryImpulse μ L t) input k := by
  simp_rw [M.zeroLatent_state]
  exact forced_observation _ _ _ _ _ _

/-- The zero-state latent output solves the full discounted polynomial equation. -/
theorem zeroLatent_equation {μ L : ℝ} (hμL : μ<L) (t : ℝ) (input : ℕ→E) (k : ℕ) :
    (∑ j : Fin (M.memory+1),M.discountedCoeff μ L t j • M.zeroLatent μ L t input (k+j.val))=
      input k := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  simp_rw [M.zeroLatent_state]
  have hlast : k+M.memory=k+1+M.lastIndex.val := by
    dsimp [lastIndex]
    have :=M.memory_pos
    omega
  rw [hlast,M.zeroLatent_state]
  have hi : ¬M.lastIndex.val+1<M.memory:=by
    dsimp [lastIndex]
    have :=M.memory_pos
    omega
  rw [forcedState_succ]
  simp only [hi,↓reduceDIte,↓reduceIte,smul_add,Finset.smul_sum,smul_smul]
  have hc : M.discountedCoeff μ L t (Fin.last M.memory)*M.inputScale μ L t=1 :=
    mul_inv_cancel₀ (M.discountedCoeff_top_ne hμL t)
  have hcoeff (j : Fin M.memory) :
      M.discountedCoeff μ L t (Fin.last M.memory)*M.realTransitionCoeff μ L t j=
        -M.discountedCoeff μ L t j.castSucc := by
    unfold realTransitionCoeff
    field_simp [M.discountedCoeff_top_ne hμL t]
  simp only [hc,hcoeff,neg_smul,Finset.sum_neg_distrib,one_smul]
  abel

/-- The literal Lur'e decomposition of every original query trajectory. -/
theorem query_response {μ L : ℝ} (hμL : μ<L) (t : ℝ) (w σ : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (M.memory+1),M.normalizedCoeff μ L j • w (k+j))=σ k) (k : ℕ) :
    Real.exp (-(k:ℝ)*t) • M.query w k=
      convolution (M.queryImpulse μ L t) (fun n=>Real.exp (-(n:ℝ)*t) • σ n) k+
        freeObservation (M.realTransitionCoeff μ L t) (M.discountedQueryCoeff t)
          (M.discountedHistory t w 0) k := by
  rw [M.discounted_query]
  simp_rw [M.discountedHistory_decomposition hμL t w σ hw,smul_add]
  rw [Finset.sum_add_distrib,forced_observation]
  exact add_comm _ _

end Vector
end
end nesterov.StationaryMethod
