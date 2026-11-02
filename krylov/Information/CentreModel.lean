import krylov.Information.FlagReflection
import krylov.Secant.TerminalRadius

/-!
Article: main_krylov, thm:centre, latest information and opposite terminal operators.
Use: identify the explicitly constructed twin's actual terminal operator with
reflection about the data-only model; reuse the existing two-scenario radius.
Source: the exact secant flag identity and the proved pointwise information bound.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Secant
open scoped BigOperators Matrix.Norms.L2Operator
variable {p : ℕ}

/-- Intermediate correction operators include their own independently budgeted perturbations.
Use: preservation must cover actual correction observations as well as probes.
Article: main_krylov, s4:C, B_k=A_k+F_k. -/
def Scenario.intermediate (S : Scenario p) (k : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  S.probe k+S.correction k

/-- The terminal correction operator uses the terminal perturbation E′.
Use: distinguish the final information uncertainty from intermediate correction data.
Article: main_krylov, s4:C, B_(n−1)=A_(n−1)+E′. -/
def Scenario.lastOperator (S : Scenario p) (N : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  S.probe N+S.terminal

/-- The exact hidden curvature accumulated at the terminal time.
Use: the information centre has this signed operator error on the two scenarios.
Article: main_krylov, apD:centre, Δ=ΣΠ_lᵀ E_l Π_l+E′. -/
def Scenario.hiddenPart (S : Scenario p) (N : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  S.oldPart N+S.terminal

/-- Consecutive actual probe operators differ by the prescribed increment.
Use: apply the existing latest-information telescoping identity to scenarios.
Article: main_krylov, s4:C, A_(k+1)−A_k=E_k.
Proof: split the finite sum at its last summand and cancel the common prefix. -/
theorem Scenario.probe_succ (S : Scenario p) (k : ℕ) :
    S.probe (k+1)=S.probe k+S.increment k := by
  simp only [Scenario.probe,sum_range_succ]
  abel

/-- The actual probe increment identity in the difference convention of the flag theorem.
Use: avoid a new proof of the latest-information telescoping calculation.
Article: main_krylov, lem:flag, consecutive compressed operators.
Proof: subtract the preceding operator from the proved successor formula. -/
theorem Scenario.probe_succ_sub (S : Scenario p) (k : ℕ) :
    S.probe (k+1)-S.probe k=S.increment k := by
  rw [S.probe_succ]
  abel

/-- Symmetric scenario inputs give symmetric actual probe operators.
Use: the latest-information flag theorem applies to the actual scenario sequence.
Article: main_krylov, s4:C, symmetric probe operators.
Proof: transpose the finite sum of symmetric increments and its symmetric base. -/
theorem Scenario.probe_isSymm (S : Scenario p) (hA : S.base.IsSymm)
    (hE : ∀ l, (S.increment l).IsSymm) (k : ℕ) : (S.probe k).IsSymm := by
  change (S.probe k)ᵀ=S.probe k
  simp only [Scenario.probe,transpose_add,transpose_sum,hA.eq]
  congr 1
  exact sum_congr rfl (fun l _ => (hE l).eq)

/-- Reflected intermediate operators differ only on directions strictly after the current prefix.
Use: every correction in the current direction span receives the identical action.
Article: main_krylov, thm:centre, cancellation by F_k^♯=F_k+2𝒴_k.
Proof: the explicit correction change cancels precisely the past old-block sum
in the proved twin probe displacement. -/
theorem Scenario.reflect_intermediate_sub (S : Scenario p) {k N : ℕ} (hk : k ≤ N) :
    (S.reflect N).intermediate k-S.intermediate k =
      (2 : ℝ) • ∑ l ∈ Ico k N,
        complementProjection p l*S.increment l*complementProjection p l := by
  -- The prescribed correction perturbation cancels the entire past old-block difference.
  have h := S.reflect_probe_sub hk
  simp only [Scenario.intermediate,Scenario.reflect]
  dsimp only [Scenario.reflect] at h
  ext i j
  have hi := congrFun (congrFun h i) j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at hi ⊢
  linarith

/-- Each intermediate correction operator preserves every column in the current prefix.
Use: extend observation preservation from the search direction to all admissible correction directions.
Article: main_krylov, thm:centre, B_k^♯=B_k on 𝒱_k.
Proof: each remaining future complementary block annihilates a prefix coordinate. -/
theorem Scenario.reflect_intermediate_column (S : Scenario p) {k N : ℕ}
    (hk : k ≤ N) (j : Fin p) (hj : j.val ≤ k) (i : Fin p) :
    (S.reflect N).intermediate k i j=S.intermediate k i j := by
  -- Every future complementary block annihilates every current-prefix coordinate.
  have hz : (∑ l ∈ Ico k N,
      complementProjection p l*S.increment l*complementProjection p l) i j=0 := by
    simp only [Matrix.sum_apply]
    apply sum_eq_zero
    intro l hl
    rw [complement_compression_apply,ite_eq_right]
    have hkl := (mem_Ico.mp hl).1
    omega
  have hd := congrFun (congrFun (S.reflect_intermediate_sub hk) i) j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,hz,mul_zero] at hd
  exact sub_eq_zero.mp hd

/-- The constructed terminal operator is reflected about the hidden-part midpoint.
Use: obtain a real pair of opposite terminal errors, not an assumed abstract pair.
Article: main_krylov, thm:centre, B_(n−1)^♯=B_(n−1)−2Δ.
Proof: the future hidden-block sum is empty at terminal time; both old curvature
and the terminal perturbation change sign. -/
theorem Scenario.reflect_lastOperator (S : Scenario p) (N : ℕ) :
    (S.reflect N).lastOperator N=S.lastOperator N-(2 : ℝ) • S.hiddenPart N := by
  -- At terminal time the future hidden-block sum is empty.
  have hd := S.reflect_probe_sub (le_refl N)
  simp only [Ico_self,sum_empty,smul_zero,zero_sub] at hd
  simp only [Scenario.lastOperator,Scenario.hiddenPart,Scenario.reflect]
  dsimp only [Scenario.reflect] at hd
  ext i j
  have hi := congrFun (congrFun hd i) j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.neg_apply] at hi ⊢
  linarith

/-- The last prefix projection in a full direction basis is the identity.
Use: cancel the artificial final increment in the existing secant flag identity.
Article: main_krylov, apD:centre, full nondegenerate direction window.
Proof: every index of Fin(N+1) is at most N. -/
theorem final_prefixProjection (N : ℕ) : prefixProjection (N+1) N=1 := by
  unfold prefixProjection
  have he : (fun i : Fin (N+1) => if i.val ≤ N then (1 : ℝ) else 0) = 1 := by
    funext i
    simp only [Nat.le_of_lt_succ i.isLt,ite_true,Pi.one_apply]
  rw [he]
  exact Matrix.diagonal_one

/-- In a full direction basis the actual latest-information model misses exactly the old-block sum.
Use: identify the data-computed centre with the midpoint of the constructed operators.
Article: main_krylov, thm:centre, A_(n−1)−T_D=Σ I_≤l E_l I_≤l.
Proof: specialize the existing flag theorem, split its last summand and cancel
the final increment using the full-prefix identity. -/
theorem Scenario.latest_probe_error {N : ℕ} (S : Scenario (N+1))
    (hA : S.base.IsSymm) (hE : ∀ l, (S.increment l).IsSymm) :
    S.probe N-latest (observed S.probe)=S.oldPart N := by
  -- Cancel the artificial final increment in the existing full-window telescoping identity.
  have hf := model_error_eq_sum_compressions S.probe (S.probe_isSymm hA hE)
  simp_rw [S.probe_succ_sub] at hf
  rw [sum_range_succ,final_prefixProjection,Matrix.one_mul,Matrix.mul_one] at hf
  calc
    S.probe N-latest (observed S.probe) =
        (S.probe (N+1)-latest (observed S.probe))-S.increment N := by
      rw [S.probe_succ]
      abel
    _ = _ := by rw [hf]; exact add_sub_cancel_right _ _

/-- The hidden part is exactly the actual terminal error relative to the data-only centre.
Use: the information centre is derived from measured probes for the constructed scenario.
Article: main_krylov, thm:centre, B_(n−1)−J_D=Δ.
Proof: add the actual terminal perturbation to the already proved latest-model error. -/
theorem Scenario.lastOperator_sub_latest {N : ℕ} (S : Scenario (N+1))
    (hA : S.base.IsSymm) (hE : ∀ l, (S.increment l).IsSymm) :
    S.lastOperator N-latest (observed S.probe)=S.hiddenPart N := by
  -- The actual terminal perturbation adds to the measured-model error.
  have h := S.latest_probe_error hA hE
  simp only [Scenario.lastOperator,Scenario.hiddenPart]
  ext i j
  have hi := congrFun (congrFun h i) j
  simp only [Matrix.sub_apply,Matrix.add_apply] at hi ⊢
  linarith

/-- The explicit twin terminal operator is reflection about the actual observed latest model.
Use: the information symmetry is tied to the source's data-computed centre.
Article: main_krylov, thm:centre, B_(n−1)^♯=2J_D−B_(n−1).
Proof: combine the actual terminal transformation with the measured-model error identity. -/
theorem Scenario.reflect_about_latest {N : ℕ} (S : Scenario (N+1))
    (hA : S.base.IsSymm) (hE : ∀ l, (S.increment l).IsSymm) :
    (S.reflect N).lastOperator N=
      (2 : ℝ) • latest (observed S.probe)-S.lastOperator N := by
  -- Identify the actual terminal midpoint through the proved latest-model error.
  rw [S.reflect_lastOperator]
  have h := S.lastOperator_sub_latest hA hE
  ext i j
  have hi := congrFun (congrFun h i) j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] at hi ⊢
  linarith

/-- Every seminorm sees at least the centred radius on one of the two constructed terminal operators.
Use: the information-centre lower bound holds before metric budget admissibility is imposed.
Article: main_krylov, thm:centre, seminorm centre assertion.
Proof: substitute the proved actual terminal reflection in the existing
seminorm reflection inequality for an arbitrary data-based model. -/
theorem Scenario.latest_seminorm_lower {N : ℕ} (S : Scenario (N+1))
    (hA : S.base.IsSymm) (hE : ∀ l, (S.increment l).IsSymm)
    (ν : Seminorm ℝ (Matrix (Fin (N+1)) (Fin (N+1)) ℝ))
    (K : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    ν (S.lastOperator N-latest (observed S.probe)) ≤
      max (ν (S.lastOperator N-K)) (ν ((S.reflect N).lastOperator N-K)) := by
  rw [S.reflect_about_latest hA hE]
  exact krylov.LinearAlgebra.reflected_seminorm ν _ _ K

end
end krylov.Information
