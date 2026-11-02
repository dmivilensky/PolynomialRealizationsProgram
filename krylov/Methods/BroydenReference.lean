import krylov.Methods.BroydenReferenceModel

set_option autoImplicit false
/-!
Article: main_krylov, def:classes, genuine global convex Broyden CG consistency.
Use: prove actual all-iteration quadratic execution and global CG consistency for the real positive-scalar-initialized full convex inverse Broyden executor.
Source: genuine accumulated-model positive direction scales, true stopped-gradient persistence and actual scale-invariant exact-search reference execution.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine inverse convex Broyden model produces a positive actual CG direction multiple on every true positive quadratic reference, including solved tails.
Use: The genuine inverse convex Broyden model produces a positive actual CG direction multiple on every true positive quadratic reference, including solved tails.
Article: main_krylov, def:classes, genuine global convex Broyden CG consistency.
Proof: Use the actual active-prefix invariant; at a real zero gradient the true linear model and actual CG direction both vanish. -/
theorem inverseBroydenModel_reference (c : ℝ) (hc : 0<c) (θ : ℕ → ℝ) (hθ : ∀ i,0≤θ i ∧ θ i≤1)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    ∃ a : ℝ,0<a ∧ -inverseBroydenModel c θ (referencePairs Q g k) (CG.gradient Q g k)=a • CG.direction Q g k := by
  -- The true zero-gradient branch requires no inverse domain; the actual linear model and genuine stopped CG direction both vanish.
  by_cases hg : CG.gradient Q g k=0
  · refine ⟨1,zero_lt_one,?_⟩
    rw [hg,map_zero,neg_zero,direction_zero_of_gradient Q g k hg,smul_zero]
  · have hpre : ∀ i<k,CG.gradient Q g i≠0 := by
      intro i hi hz
      exact hg (CG.gradient_eq_zero_of_le Q g hz hi.le)
    obtain ⟨a,ha,hg',_⟩ := inverseBroydenModel_reference_prefix c hc θ hθ Q hQ hpos g k hpre k le_rfl
    refine ⟨a,ha,?_⟩
    rw [hg',neg_smul,neg_neg]

/-- The actual convex Broyden policy read from a genuine reference transcript chooses a true positive CG direction multiple.
Use: The actual convex Broyden policy read from a genuine reference transcript chooses a true positive CG direction multiple.
Article: main_krylov, def:classes, genuine global convex Broyden CG consistency.
Proof: Identify the actual observed gradient and complete pair list before applying the genuine model invariant. -/
theorem broydenMethod_direction (c : ℝ) (hc : 0<c) (θ : ℕ → ℝ) (hθ : ∀ i,0≤θ i ∧ θ i≤1)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) (H : History E)
    (hg : H.gradient=CG.gradient Q g k) (hp : H.pairs=referencePairs Q g k) :
    ∃ a : ℝ,0<a ∧ (broydenMethod c θ).direction H=a • CG.direction Q g k := by
  change ∃ a : ℝ,0<a ∧ -inverseBroydenModel c θ H.pairs H.gradient=a • CG.direction Q g k
  rw [hg,hp]
  exact inverseBroydenModel_reference c hc θ hθ Q hQ hpos g k

/-- The real convex Broyden executor has exactly the genuine CG quadratic gradients and recorded secant pairs for every iteration.
Use: The real convex Broyden executor has exactly the genuine CG quadratic gradients and recorded secant pairs for every iteration.
Article: main_krylov, def:classes, genuine global convex Broyden CG consistency.
Proof: Induct through actual execution; the real positive CG direction scale cancels in the true exact search. -/
theorem broydenMethod_static (c : ℝ) (hc : 0<c) (θ : ℕ → ℝ) (hθ : ∀ i,0≤θ i ∧ θ i≤1)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    let H := methodRun (broydenMethod c θ) (fun _ => Q) (fun _ => Q) g k
    H.gradient=CG.gradient Q g k ∧ H.pairs=referencePairs Q g k := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    obtain ⟨a,ha,hd⟩ := broydenMethod_direction c hc θ hθ Q hQ hpos g k _ ih.1 ih.2
    exact reference_advance_scaled _ Q g k _ ih.1 ih.2 ha.ne' hd trivial

/-- The actual positive-scalar-initialized full inverse convex Broyden method is genuinely globally CG-consistent.
Use: The actual positive-scalar-initialized full inverse convex Broyden method is genuinely globally CG-consistent.
Article: main_krylov, def:classes, genuine global convex Broyden CG consistency.
Proof: Use the real full reference transcript, actual positive direction multiple and genuine empty correction phase. -/
theorem broydenMethod_consistent (c : ℝ) (hc : 0<c) (θ : ℕ → ℝ) (hθ : ∀ i,0≤θ i ∧ θ i≤1) :
    CGConsistent (broydenMethod c θ : ProbedMethod E) := by
  intro Q hQ hpos g k
  have hs := broydenMethod_static c hc θ hθ Q hQ hpos g k
  obtain ⟨a,ha,hd⟩ := broydenMethod_direction c hc θ hθ Q hQ hpos g k _ hs.1 hs.2
  exact ⟨a,ha,hd,trivial⟩
end
end krylov.Methods
