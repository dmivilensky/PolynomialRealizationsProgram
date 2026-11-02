import krylov.Functions.ReferencePlaneValueFibre

/-!
Article: main_krylov, thm:Fplanar, genuine single final correction rules.
Use: construct data-only retained-span corrections that perform zero motion
on every positive quadratic CG history, including genuine solved tails.
Source: true CG residual orthogonality, with zero-gradient persistence.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The last actually observed gradient of a searched cycle.
Article: main_krylov, thm:Fplanar. -/
def observedFinalGradient {N : ℕ} (data : FunctionSearchTranscript E N) : E :=
  data.gradients ⟨N,Nat.lt_succ_self N⟩

/-- The last actually searched point, before the single final correction.
Article: main_krylov, thm:Fplanar. -/
def observedFinalPoint {N : ℕ} (data : FunctionSearchTranscript E N) : E :=
  data.points ⟨N,Nat.lt_succ_self N⟩

/-- An arbitrary finite retained-span final displacement, gated by the
actual observed first-step residual pairing. Every coefficient may use all
observed scalar data. Article: main_krylov, thm:Fplanar. -/
def observedSpanFinalCorrection {N : ℕ} (hN : 0<N)
    (coeff : History E → FunctionSearchTranscript E N → Fin N → ℝ)
    (H : History E) (data : FunctionSearchTranscript E N) : E := by
  classical
  exact if inner ℝ (observedFinalGradient data) (data.lineSteps ⟨0,hN⟩)=0 then 0
    else ∑ i,coeff H data i • data.lineSteps i

/-- Apply one genuine retained-span correction after the actual searched
endpoint, before its one new gradient evaluation. Article: thm:Fplanar. -/
def observedSpanFinalPolicy {N : ℕ} (hN : 0<N)
    (coeff : History E → FunctionSearchTranscript E N → Fin N → ℝ)
    (H : History E) (data : FunctionSearchTranscript E N) : E :=
  observedFinalPoint data+observedSpanFinalCorrection hN coeff H data

/-- The directly observed zero residual pairing makes the selected output
exactly the already searched endpoint. Article: thm:Fplanar. -/
theorem observedSpanFinalPolicy_guard_zero {N : ℕ} (hN : 0<N)
    (coeff : History E → FunctionSearchTranscript E N → Fin N → ℝ)
    (H : History E) (data : FunctionSearchTranscript E N)
    (hz : inner ℝ (observedFinalGradient data) (data.lineSteps ⟨0,hN⟩)=0) :
    observedSpanFinalPolicy hN coeff H data=observedFinalPoint data := by
  classical
  rw [observedSpanFinalPolicy,observedSpanFinalCorrection,ite_eq_left hz,add_zero]

/-- The selected final displacement always belongs to the retained real
step span, for arbitrary scalar data and arbitrary coefficient decisions.
Article: main_krylov, def:classes and thm:Fplanar. -/
theorem observedSpanFinalCorrection_mem {N : ℕ} (hN : 0<N)
    (coeff : History E → FunctionSearchTranscript E N → Fin N → ℝ)
    (H : History E) (data : FunctionSearchTranscript E N) :
    observedSpanFinalCorrection hN coeff H data∈Submodule.span ℝ (Set.range data.lineSteps) := by
  classical
  unfold observedSpanFinalCorrection
  split
  · exact Submodule.zero_mem _
  · exact Submodule.sum_mem _ (fun i _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))

/-- True quadratic post-search residuals are orthogonal to every retained
old step, also after actual early CG termination.
Article: main_krylov, thm:Fplanar, global quadratic consistency. -/
theorem quadratic_final_gradient_first_step (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) {N : ℕ} (hN : 0<N) :
    inner ℝ (CG.gradient Q g N) (referenceStep Q g 0)=0 := by
  by_cases hpre : ∀ j<N, CG.gradient Q g j≠0
  · rw [real_inner_comm]
    have ho := referenceStep_postsearch_orth Q hQ hpos g (N-1)
      (fun j hj=>hpre j (by omega)) (i:=0) (by omega)
    simpa only [Nat.sub_add_cancel hN] using ho
  · push Not at hpre
    obtain ⟨j,hj,hz⟩ := hpre
    rw [CG.gradient_eq_zero_of_le Q g hz hj.le,inner_zero_left]

/-- Every constructed one-query final rule makes exactly zero correction
on every true positive quadratic CG transcript. This is derived from CG,
independently of all supplied scalar values and all policy coefficients.
Article: main_krylov, thm:Fplanar, admissible global quadratic behaviour. -/
theorem observedSpanFinalCorrection_quadratic_zero {N : ℕ} (hN : 0<N)
    (coeff : History E → FunctionSearchTranscript E N → Fin N → ℝ)
    (H : History E) (data : FunctionSearchTranscript E N)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hg : observedFinalGradient data=CG.gradient Q g N)
    (hs : data.lineSteps ⟨0,hN⟩=referenceStep Q g 0) :
    observedSpanFinalCorrection hN coeff H data=0 := by
  classical
  rw [observedSpanFinalCorrection,hg,hs,
    ite_eq_left (quadratic_final_gradient_first_step Q hQ hpos g hN)]

/-- Compile the retained-span rule into exactly one genuine final gradient
query. Its decision is made before observing that new gradient.
Article: main_krylov, def:classes and thm:Fplanar. -/
def observedSpanFinalTree {N : ℕ} (hN : 0<N)
    (coeff : History E → FunctionSearchTranscript E N → Fin N → ℝ)
    (H : History E) (data : FunctionSearchTranscript E N) : CorrectionTree E :=
  .query (observedSpanFinalCorrection hN coeff H data) (fun _=>.done)

/-- The compiled original correction evaluates the actual gradient at the
selected physical final output and has no further adaptive queries.
Article: main_krylov, thm:Fplanar. -/
theorem observedSpanFinalTree_execute {N : ℕ} (hN : 0<N)
    (coeff : History E → FunctionSearchTranscript E N → Fin N → ℝ)
    (H : History E) (data : FunctionSearchTranscript E N) (G : E → E) :
    scalarFunctionCorrections (observedSpanFinalTree hN coeff H data) G (observedFinalPoint data)=
      ⟨observedSpanFinalCorrection hN coeff H data,
        G (observedSpanFinalPolicy hN coeff H data),
        [(observedSpanFinalCorrection hN coeff H data,G (observedSpanFinalPolicy hN coeff H data))]⟩ := by
  simp only [observedSpanFinalTree,scalarFunctionCorrections,observedSpanFinalPolicy,add_zero]

end
end krylov.Functions
