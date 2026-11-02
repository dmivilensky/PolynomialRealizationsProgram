import krylov.Stability.ReferenceWeights
import krylov.Methods.ExecutedFC
import krylov.Methods.CanonicalWindows

/-!
Article: main_krylov, apB:lem:UAsteps, true accumulated-gradient stability.
Use: derive actual canonical FC gradient errors from genuine earlier step
errors and real operator budgets, uniformly near arbitrarily small CG energies.
Source: exact actual secant updates, finite telescoping and the proved true
CG energy drops and error monotonicity; no differentiability assumption is used.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual accumulated linear-oracle gradients differ from the true identity-reference updates by the exact finite step-error and operator-drift bound.
Use: the uniform induction controls real observed gradients from earlier actual steps, rather than assuming a gradient approximation.
Article: main_krylov, apB:lem:UAsteps.
Proof: subtract the two genuine next-gradient equations. The difference
splits into the previous real gradient error, the actual step error and the
true operator deviation acting on the actual step; sum the norm bounds. -/
theorem running_gradient_difference_bound (G G₀ s s₀ : ℕ → E) (B : ℕ → E →L[ℝ] E)
    (hinit : G 0=G₀ 0) (hG : ∀ i, G (i+1)=G i+B i (s i))
    (hG₀ : ∀ i, G₀ (i+1)=G₀ i+s₀ i) (N : ℕ) :
    ‖G N-G₀ N‖≤∑ i∈Finset.range N,
      (‖s i-s₀ i‖+‖B i-ContinuousLinearMap.id ℝ E‖*‖s i‖) := by
  -- The genuine next-gradient difference keeps the drift acting on the actual step.
  induction N with
  | zero => simp only [hinit,sub_self,norm_zero,Finset.sum_range_zero,le_refl]
  | succ N ih =>
    have he : G (N+1)-G₀ (N+1)=((G N-G₀ N)+(s N-s₀ N))+
        (B N-ContinuousLinearMap.id ℝ E) (s N) := by
      rw [hG,hG₀]
      change G N+B N (s N)-(G₀ N+s₀ N)=((G N-G₀ N)+(s N-s₀ N))+(B N (s N)-s N)
      abel
    rw [he,Finset.sum_range_succ]
    have ht := norm_add_le ((G N-G₀ N)+(s N-s₀ N)) ((B N-ContinuousLinearMap.id ℝ E) (s N))
    have hp := norm_add_le (G N-G₀ N) (s N-s₀ N)
    have ho := (B N-ContinuousLinearMap.id ℝ E).le_opNorm (s N)
    linarith

/-- True earlier step errors bounded by Cδ and actual operator deviations bounded by δ give the uniform accumulated-gradient bound N(2C+1)δ.
Use: the finite induction constant depends on the horizon and prior constant, with no inverse reference energy or step length.
Article: main_krylov, apB:lem:UAsteps.
Proof: each actual step has norm at most one plus its genuine reference
error. Apply the exact finite gradient bound and use δ≤1 in its quadratic
term, then count the true chronological steps. -/
theorem running_gradient_uniform_bound (G G₀ s s₀ : ℕ → E) (B : ℕ → E →L[ℝ] E)
    (hinit : G 0=G₀ 0) (hG : ∀ i, G (i+1)=G i+B i (s i))
    (hG₀ : ∀ i, G₀ (i+1)=G₀ i+s₀ i) (N : ℕ) {δ C : ℝ}
    (hδ : 0≤δ) (hδone : δ≤1) (hC : 0≤C)
    (hB : ∀ i<N, ‖B i-ContinuousLinearMap.id ℝ E‖≤δ)
    (href : ∀ i<N, ‖s₀ i‖≤1) (hs : ∀ i<N, ‖s i-s₀ i‖≤C*δ) :
    ‖G N-G₀ N‖≤(N : ℝ)*(2*C+1)*δ := by
  -- All terms share the real finite horizon; the quadratic drift-times-step error uses δ≤1.
  apply (running_gradient_difference_bound G G₀ s s₀ B hinit hG hG₀ N).trans
  calc
    _ ≤ ∑ _i∈Finset.range N, (2*C+1)*δ := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN := Finset.mem_range.mp hi
      have hsn : ‖s i‖≤C*δ+1 := (norm_le_norm_sub_add (s i) (s₀ i)).trans (add_le_add (hs i hiN) (href i hiN))
      have hm := mul_le_mul (hB i hiN) hsn (norm_nonneg _) hδ
      have hd := mul_le_mul_of_nonneg_left hδone (mul_nonneg hC hδ)
      nlinarith [hs i hiN]
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

variable {n : ℕ}

/-- Every genuine canonical CG step is bounded by the true initial canonical error norm, including stopped tails.
Use: discharge the reference-step size premise in the actual uniform gradient induction.
Article: main_krylov, apB:lem:UAsteps.
Proof: the true energy drop bounds the actual step by the current error;
the proved real CG error monotonicity bounds that error by the initial one. -/
theorem canonicalCGStep_norm_le_initial (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ‖canonicalCGStep base g k‖≤‖cgCanonicalError base g 0‖ := by
  have hd := cgEnergy_drop base hb g k
  rw [cgEnergy_eq_norm_sq base hb] at hd
  have hs : ‖canonicalCGStep base g k‖≤‖cgCanonicalError base g k‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith [sq_nonneg ‖cgCanonicalError base g (k+1)‖]
  exact hs.trans (cgError_antitone base hb g (Nat.zero_le k))

/-- The actual FC canonical gradient has the uniform finite-horizon bound derived from its real earlier step errors and true canonical operator budgets.
Use: the actual accumulation part of the source FC stability induction is fully discharged, with the genuine initial-error normalization.
Article: main_krylov, apB:lem:UAsteps.
Proof: the actual executed FC update transfers through the real positive
metric root to the genuine canonical oracle update. The true CG energy
drop bounds each reference step; apply the proved uniform finite accumulation
estimate to these actual and reference trajectories. -/
theorem fullFC_canonical_gradient_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) {δ C : ℝ}
    (hδ : 0≤δ) (hδone : δ≤1) (hC : 0≤C) (hinit : ‖cgCanonicalError base g 0‖≤1)
    (hA : ∀ i<N, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤δ)
    (hs : ∀ i<N, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i)-canonicalCGStep base g i‖≤C*δ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (fcGradient fullMemory A g N)-cgCanonicalError base g N‖≤
      (N : ℝ)*(2*C+1)*δ := by
  -- Use the actual executed canonical gradients in the accumulation theorem.
  apply running_gradient_uniform_bound
    (fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (fcGradient fullMemory A g i))
    (cgCanonicalError base g)
    (fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i))
    (canonicalCGStep base g) (fun i => canonicalOperator base (A i)) rfl _
    (cgCanonicalError_succ base hb g) N hδ hδone hC hA
    (fun i _ => (canonicalCGStep_norm_le_initial base hb g i).trans hinit) hs
  intro i
  rw [fcGradient_succ,fcSecant,canonical_gradient_update base hb]
end
end krylov.Stability
