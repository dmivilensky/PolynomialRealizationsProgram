import krylov.Methods.QuadraticCycles

/-!
Article: main_krylov, lem:consistent(a), RFC-S with an exact quadratic probe.
Use: distinguish the secant probe operator from the actual line and correction
segments, then prove real transcript equality when the probe is exact.
Source: RFC-S in Appendix D and its exact-quadratic specialization.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One actual RFC-S iteration with a separate secant probe operator and genuine physical segment updates.
Use: the predicted post-search gradient is used only for the data-only model solve; the recorded gradient comes from the actual evaluated displacement.
Article: main_krylov, lem:consistent(a) and thm:RFCS, Aᵖ, A and B. -/
def rfcSAdvance (memory : ℕ → ℕ) (Ap A B : E →L[ℝ] E) (H : History E) : History E :=
  let W := selectedWindow memory H
  let d := windowDirection W H.gradient
  let z := Ap d
  let line := lineLength H.gradient d z • d
  let U := (d,z)::W
  if W≠[] ∧ ‖windowDefect W‖<1 then
    let u := combine (windowSteps U) (modelCoefficients (windowSteps U) (windowModel U)
      (searchedGradient H.gradient d z))
    let gnew := H.gradient+A line+B u
    ⟨H.initial,⟨d,z,line+u,gnew,[(u,gnew)]⟩::H.records⟩
  else
    ⟨H.initial,⟨d,z,line,H.gradient+A line,[]⟩::H.records⟩

/-- The actual RFC-S run with independently prescribed probe, line and correction segment operators.
Use: its data history contains only genuine physical observations and its secant probe actions.
Article: main_krylov, lem:consistent(a), RFC-S exact-probe case. -/
def rfcSRun (memory : ℕ → ℕ) (Ap A B : ℕ → E →L[ℝ] E) (g : E) : ℕ → History E
  | 0 => ⟨g,[]⟩
  | k+1 => rfcSAdvance memory (Ap k) (A k) (B k) (rfcSRun memory Ap A B g k)

/-- An exact secant probe makes an actual RFC-S iteration identical to the actual single-correction RFC iteration.
Use: quadratic RFC-S consistency is discharged by a real algorithmic transcript identity.
Article: main_krylov, lem:consistent(a), Aᵖ=A.
Proof: exact probe linearity identifies the predicted and actual line gradient;
the two policies then perform the same model solve, correction and actual observation in each gate branch. -/
theorem rfcSAdvance_exact (memory : ℕ → ℕ) (A B : E →L[ℝ] E) (H : History E) :
    rfcSAdvance memory A A B H=methodAdvance (rfcMethod memory 1) A B H := by
  -- The output record, including its actual correction observation, agrees in both gate branches.
  unfold rfcSAdvance methodAdvance rfcMethod retainedMethod rfcCorrection
  dsimp only
  split <;> simp only [repeatedModelTree,runCorrections,searchedGradient,map_smul,add_zero]

/-- Every exact-probe RFC-S run has exactly the actual RFC observed history.
Use: transfers all proved full, positive sliding and active-cycle restarted quadratic assertions to RFC-S.
Article: main_krylov, lem:consistent(a), exact quadratic probes.
Proof: induction applies the exact real iteration identity on the common actual observed history. -/
theorem rfcSRun_exact (memory : ℕ → ℕ) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    rfcSRun memory A A B g k=methodRun (rfcMethod memory 1) A B g k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rfcSRun,ih,rfcSAdvance_exact]; rfl

/-- With exact static quadratic probes, the actual RFC-S gradients, stored pairs and physical points are the true CG quantities.
Use: proves the source's RFC-S specialization for every newest-retaining regime, including actual active-cycle restarts.
Article: main_krylov, lem:consistent(a), RFC-S quadratic consistency.
Proof: exact-probe transcript equality reduces the actual run to the already
proved actual RFC reference transcript, which determines its real physical displacement. -/
theorem rfcSRun_static (memory : ℕ → ℕ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hm : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<memory k) (k : ℕ) :
    let H := rfcSRun memory (fun _ => Q) (fun _ => Q) (fun _ => Q) g k
    H.gradient=CG.gradient Q g k ∧ H.pairs=referencePairs Q g k ∧
      H.displacement=CG.displacement Q g k := by
  rw [rfcSRun_exact]
  have hs := rfcMethod_static memory 1 Q hQ hpos g hm k
  exact ⟨hs.1,hs.2,History.displacement_reference _ _ _ _ hs.2⟩

end
end krylov.Methods
