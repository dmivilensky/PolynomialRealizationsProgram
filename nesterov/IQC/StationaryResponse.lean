import nesterov.IQC.StateResponse
import nesterov.IQC.PolynomialStability

/-!
The Lur'e decomposition of the literal finite-memory executor. The state is
discounted coordinate by coordinate, so its transition is the stable companion
of p(exp(t) z), and the query remains the article's original linear query.
-/
namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
open nesterov.IQC polyak.General.IQC
variable (M : nesterov.StationaryMethod)

/-- Real coefficients of the discounted companion. -/
def realTransitionCoeff (μ L t : ℝ) (j : Fin M.memory) : ℝ :=
  -(M.discountedCoeff μ L t j.castSucc/M.discountedCoeff μ L t (Fin.last M.memory))

@[simp] theorem coe_realTransitionCoeff (μ L t : ℝ) (j : Fin M.memory) :
    (M.realTransitionCoeff μ L t j:ℂ)=M.transitionCoeff μ L t j := by
  simp only [realTransitionCoeff,transitionCoeff,Complex.ofReal_neg]

/-- Input gain at the last coordinate of the discounted companion. -/
def inputScale (μ L t : ℝ) : ℝ :=
  (M.discountedCoeff μ L t (Fin.last M.memory))⁻¹

/-- Last coordinate of the full memory, also for memory one. -/
def lastIndex : Fin M.memory:=⟨M.memory-1,by have := M.memory_pos; omega⟩

section Vector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complete discounted history, retaining every latent coordinate. -/
def discountedHistory (t : ℝ) (w : ℕ→E) (k : ℕ) (j : Fin M.memory) : E :=
  Real.exp (-((k+j.val:ℕ):ℝ)*t) • w (k+j.val)

/-- The normalized recursion after discounting, before solving its final coefficient. -/
theorem discounted_equation (μ L t : ℝ) (w σ : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (M.memory+1),M.normalizedCoeff μ L j • w (k+j))=σ k)
    (k : ℕ) :
    (∑ j : Fin M.memory,M.discountedCoeff μ L t j.castSucc •
      M.discountedHistory t w k j)+
      M.discountedCoeff μ L t (Fin.last M.memory) •
        M.discountedHistory t w (k+1) M.lastIndex=
      Real.exp (-(k:ℝ)*t) • σ k := by
  rw [←hw k,Finset.smul_sum,Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  have he (j : ℕ) : Real.exp (j*t)*Real.exp (-((k+j:ℕ):ℝ)*t)=Real.exp (-(k:ℝ)*t) := by
    rw [←Real.exp_add]
    congr 1
    push_cast
    ring
  have hlast : k+1+M.lastIndex.val=k+M.memory := by
    dsimp [lastIndex]
    have :=M.memory_pos
    omega
  simp only [discountedCoeff,discountedHistory,hlast,Fin.val_castSucc,Fin.val_last,smul_smul]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [mul_assoc,he]
    ring
  · congr 1
    rw [mul_assoc,he]
    ring


/-- Actual state evolution from the normalized stationary equation. -/
theorem discountedHistory_step {μ L : ℝ} (hμL : μ<L) (t : ℝ) (w σ : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (M.memory+1),M.normalizedCoeff μ L j • w (k+j))=σ k)
    (k : ℕ) (i : Fin M.memory) :
    M.discountedHistory t w (k+1) i=
      (if hi : i.val+1<M.memory then M.discountedHistory t w k ⟨i.val+1,hi⟩
        else ∑ j,M.realTransitionCoeff μ L t j • M.discountedHistory t w k j)+
      (if i=M.lastIndex then M.inputScale μ L t •
        (Real.exp (-(k:ℝ)*t) • σ k) else 0) := by
  by_cases hi : i.val+1<M.memory
  · have hil : i≠M.lastIndex := by
      intro hh
      rw [hh] at hi
      dsimp [lastIndex] at hi
      have :=M.memory_pos
      omega
    simp only [hi,↓reduceDIte,hil,↓reduceIte,add_zero,discountedHistory]
    simp only [show k+1+i.val=k+(i.val+1) by omega]
  · have hil : i=M.lastIndex := Fin.ext (by
      dsimp [lastIndex]
      have :=i.isLt
      have :=M.memory_pos
      omega)
    subst i
    simp only [hi,↓reduceDIte,↓reduceIte]
    have he:=M.discounted_equation μ L t w σ hw k
    have hs:=congrArg (fun y : E=>M.inputScale μ L t • y) he
    have hc : M.inputScale μ L t*M.discountedCoeff μ L t (Fin.last M.memory)=1 :=
      inv_mul_cancel₀ (M.discountedCoeff_top_ne hμL t)
    simp only [smul_add,smul_smul,hc,one_smul,Finset.smul_sum] at hs
    have hcoeff (j : Fin M.memory) :
        M.realTransitionCoeff μ L t j=
          -(M.inputScale μ L t*M.discountedCoeff μ L t j.castSucc) := by
      unfold realTransitionCoeff inputScale
      ring
    simp only [hcoeff,neg_smul,Finset.sum_neg_distrib]
    have hh:=eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hs)
    simpa only [sub_eq_add_neg,add_comm,smul_smul] using hh

/-- Exact free/forced representation of every actual normalized trajectory. -/
theorem discountedHistory_decomposition {μ L : ℝ} (hμL : μ<L) (t : ℝ) (w σ : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (M.memory+1),M.normalizedCoeff μ L j • w (k+j))=σ k)
    (k : ℕ) (i : Fin M.memory) :
    M.discountedHistory t w k i=
      freeState (M.realTransitionCoeff μ L t) (M.discountedHistory t w 0) k i+
      forcedState (M.realTransitionCoeff μ L t) (M.inputScale μ L t) M.lastIndex
        (fun n=>Real.exp (-(n:ℝ)*t) • σ n) k i :=
  state_decomposition _ _ _ _ _ _ rfl
    (M.discountedHistory_step hμL t w σ hw) k i

/-- Coefficients of the query on the discounted complete history. -/
def discountedQueryCoeff (t : ℝ) (j : Fin M.memory) : ℝ :=
  M.queryCoeff j*Real.exp (j.val*t)

/-- Query discounting agrees exactly with observation of the discounted state. -/
theorem discounted_query (t : ℝ) (w : ℕ→E) (k : ℕ) :
    Real.exp (-(k:ℝ)*t) • M.query w k=
      ∑ j,M.discountedQueryCoeff t j • M.discountedHistory t w k j := by
  simp only [query,discountedQueryCoeff,discountedHistory,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have he : Real.exp (j.val*t)*Real.exp (-((k+j.val:ℕ):ℝ)*t)=Real.exp (-(k:ℝ)*t) := by
    rw [←Real.exp_add]
    congr 1
    push_cast
    ring
  rw [mul_assoc,he]
  ring

end Vector
end
end nesterov.StationaryMethod
