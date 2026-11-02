import krylov.Nonlinear.MetricCoordinates
import krylov.Methods.RFCSHomogeneous
import krylov.Methods.RFCReference
import krylov.Correction.ReferenceOperator

/-!
Article: main_krylov, thm:RFCS, genuine quadratic cycle-reference scaling.
Use: Identify the real reference search lengths and penultimate metric error
under the true nonlinear cycle scale, including all degenerate/stopped CG tails.
Source: proved actual static RFC-S/CG transcript equality, exact real RFC-S
homogeneity and the genuine terminal CG step/error norm identity.
-/

namespace krylov.Nonlinear
noncomputable section
open krylov.Methods krylov.Reference krylov.Correction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine CG gradient recurrence is exactly homogeneous under every nonzero initial-gradient scale, including stopped tails.
Use: Identify the actual quadratic reference of each nonlinear cycle from its normalized initial direction.
Article: main_krylov, thm:RFCS, original genuine cycle-reference quantities.
Proof: Read the actual static CG gradient from the proved genuine RFC-S transcript and use its exact initial-data homogeneity.
-/
theorem reference_gradient_smul (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (c : ℝ) (hc : c≠0) (N : ℕ) :
    CG.gradient Q (c • g) N=c • CG.gradient Q g N := by
  have h₀ : rfcSGradient fullMemory (fun _ => Q) (fun _ => Q) (fun _ => Q) g N=CG.gradient Q g N :=
    (rfcSRun_static fullMemory Q hQ hpos g (fun _ _ hj => hj) N).1
  have h₁ : rfcSGradient fullMemory (fun _ => Q) (fun _ => Q) (fun _ => Q) (c • g) N=CG.gradient Q (c • g) N :=
    (rfcSRun_static fullMemory Q hQ hpos (c • g) (fun _ _ hj => hj) N).1
  rw [← h₁,← h₀]
  exact (rfcS_scalar fullMemory (fun _ => Q) (fun _ => Q) (fun _ => Q) g c hc N).1


/-- The genuine CG direction recurrence is exactly homogeneous under every nonzero initial-gradient scale.
Use: Compare actual per-cycle CG probes with their compact normalized reference family.
Article: main_krylov, thm:RFCS, original genuine cycle-reference quantities.
Proof: Identify the true static CG direction with the actual RFC-S selected field and apply its proved exact scaling.
-/
theorem reference_direction_smul (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (c : ℝ) (hc : c≠0) (N : ℕ) :
    CG.direction Q (c • g) N=c • CG.direction Q g N := by
  have h₀ : rfcSDirection fullMemory (fun _ => Q) (fun _ => Q) (fun _ => Q) g N=CG.direction Q g N := by
    rw [(rfcSFields_exact fullMemory (fun _ => Q) (fun _ => Q) g N).2.1]
    exact rfc_reference_direction fullMemory 1 Q hQ hpos g (fun _ _ hj => hj) N
  have h₁ : rfcSDirection fullMemory (fun _ => Q) (fun _ => Q) (fun _ => Q) (c • g) N=CG.direction Q (c • g) N := by
    rw [(rfcSFields_exact fullMemory (fun _ => Q) (fun _ => Q) (c • g) N).2.1]
    exact rfc_reference_direction fullMemory 1 Q hQ hpos (c • g) (fun _ _ hj => hj) N
  rw [← h₁,← h₀]
  exact ((rfcS_scalar fullMemory (fun _ => Q) (fun _ => Q) (fun _ => Q) g c hc (N+1)).2 N (Nat.lt_succ_self N)).1

/-- The true CG reference search lengths are unchanged by nonzero scaling of the actual initial gradient.
Use: Convert the source bounded per-cycle reference probe rule to its actual normalized compact reference form.
Article: main_krylov, thm:RFCS, original genuine cycle-reference quantities.
Proof: Use the genuine gradient/direction scaling and cancel the true common scalar in the measured line-length quotient.
-/
theorem reference_length_smul (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (c : ℝ) (hc : c≠0) (N : ℕ) :
    CG.length Q (c • g) N=CG.length Q g N := by
  change lineLength (CG.gradient Q (c • g) N) (CG.direction Q (c • g) N)
    (Q (CG.direction Q (c • g) N))=_
  rw [reference_gradient_smul Q hQ hpos g c hc N,reference_direction_smul Q hQ hpos g c hc N,
    map_smul,lineLength_scalar _ _ _ c hc]

variable {k n : ℕ}

/-- The genuine canonical CG error vector scales with its true initial gradient.
Use: Identify the original quadratic cycle-reference error in the source metric.
Article: main_krylov, thm:RFCS, original genuine cycle-reference quantities.
Proof: Apply the fixed genuine inverse metric root to the true scaled CG gradient.
-/
theorem cgCanonicalError_smul (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hc : c≠0) (N : ℕ) :
    cgCanonicalError base (c • g) N=c • cgCanonicalError base g N := by
  unfold cgCanonicalError
  rw [reference_gradient_smul _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g c hc N,map_smul]

/-- The actual penultimate canonical error of the scaled full CG cycle is exactly the cycle scale times the genuine original last reference step norm.
Use: Express the nonlinear RFC-S leading coefficient using the article original cycle-reference penultimate error.
Article: main_krylov, thm:RFCS, original genuine cycle-reference quantities.
Proof: Use exact real reference-error homogeneity and the proved true terminal CG step/error norm identity in the constructed metric coordinates.
-/
theorem metric_last_reference_error_norm (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g)
    {ε : ℝ} (hε : 0<ε) :
    ‖cgCanonicalError base (ε • g) k‖=ε*‖metricCoordinates base hb (referenceStep (cgOperator base) g k)‖ := by
  rw [cgCanonicalError_smul base hb g ε hε.ne' k,norm_smul,Real.norm_of_nonneg hε.le,terminal_step_error_norm base hb g hN]
  rfl

end
end krylov.Nonlinear
