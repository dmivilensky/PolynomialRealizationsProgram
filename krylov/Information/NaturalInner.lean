import krylov.Information.ForwardForms
import krylov.Information.PreQuadraticSlack

/-!
Article: main_krylov, s4:cor-Q, original pre-quadratic admissible inner slack.
Use: the stated primitive 1−4nW₀ source budget margins derive the actual
common-coordinate reflection domains and every H1--H3 requirement.
Source: genuine common CG rank, actual own-base sharp Gram defect,
exact forward relative-budget transport and proved scalar slack algebra.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The original physical inner source class with the printed budget and fixed-reference radius slack.
Use: store only genuine primitive admissibility and source budget margins, without a supplied reflected scenario or instance-comparison conclusion.
Article: main_krylov, s4:cor-Q, the actual source class S^natural. -/
structure Scenario.NaturalInner (S : Scenario (N+1)) (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) : Prop where
  /-- The original physical source satisfies every original reference-ball and individual budget constraint. -/
  original : S.Admissible N A r ω w τ
  /-- Every original increment uses the stated common 1−4nW₀ slack in its own actual base metric. -/
  increment : ∀ l<N, relativeBudget S.base (S.increment l)≤
    (1-4*((N : ℝ)+1)*(∑ i∈range N, ω i))*ω l
  /-- The independent terminal perturbation uses exactly the same original common source slack. -/
  terminal : relativeBudget S.base S.terminal≤(1-4*((N : ℝ)+1)*(∑ i∈range N, ω i))*w
  /-- The original physical base leaves precisely the stated 4(1+r)W₀ fixed-reference radius margin. -/
  base_margin : relativeBudget A (S.base-A)≤r-4*(1+r)*(∑ i∈range N, ω i)

/-- The original physical pre-quadratic inner budget margins derive the genuine common reflection inverse domain, H1--H3 and the actual hidden-base displacement bound ϖ≤4W₀.
Use: the source's stated slack is verified before constructing a common actual admissible twin, including zero profiles and the permitted slack boundary.
Article: main_krylov, s4:cor-Q, actual source slack implies the required common reflection constraints.
Proof: true full CG gives the actual common direction inverse. Its genuine
own-base Gram defect is at most (n−1)W₀. Forward form transport preserves
every original individual relative budget, hence the actual total hidden
base displacement has the proved flag-ratio bound. The exact scalar slack
theorem gives both required margins. The original physical radius margin
survives the same true coordinate transport and gives H3 directly. -/
theorem Scenario.NaturalInner.reflection_controls {S : Scenario (N+1)}
    {A Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hA : A.PosDef) (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    {r w τ : ℝ} {ω : ℕ → ℝ} (h : S.NaturalInner A r ω w τ)
    (hpre : S.PreQuadratic (cgOperator Q) g N) (hN : 0<N) (hr : 0≤r) (hw : 0≤w)
    (hsmall : 4*((N : ℝ)+1)*(∑ i∈range N, ω i)≤1) :
    let D := fullBasisMatrix (referenceDirectionColumns Q g)
    let C := S.inCoordinates D
    directionDefect C.base<1 ∧ C.twinDisplacement N<1 ∧
      (∀ l<N, relativeBudget C.base (C.increment l)≤((1-C.twinDisplacement N)/flagDistortion C.base)*ω l) ∧
      relativeBudget C.base C.terminal≤(1-C.twinDisplacement N)*w ∧
      relativeBudget (formMap D A) (C.base-formMap D A)+(1+r)*C.twinDisplacement N≤r ∧
      C.twinDisplacement N≤4*(∑ i∈range N, ω i) := by
  -- The actual common CG basis and primitive original budgets determine the genuine reflection domain.
  let D := fullBasisMatrix (referenceDirectionColumns Q g)
  let C := S.inCoordinates D
  let W := ∑ i∈range N, ω i
  let ε := directionDefect C.base
  let κ := flagDistortion C.base
  let v := C.twinDisplacement N
  have hD : IsUnit D.det := fullBasisMatrix_unit _ (referenceDirectionColumns_independent Q hQ g hcount)
  have hω (i : ℕ) (hi : i<N) : 0≤ω i := (norm_nonneg (relativeOperator S.base (S.increment i))).trans (h.original.2.2.1 i hi).2
  have hW : 0≤W := sum_nonneg fun i hi => hω i (mem_range.mp hi)
  have hε : 0≤ε := norm_nonneg _
  have hεW : ε≤(N : ℝ)*W := hpre.reference_gram_bound h.original.1 hQ hcount
    (fun i hi => (h.original.2.2.1 i hi).1) ω (fun i hi => (h.original.2.2.1 i hi).2)
  have hquarter : ε≤(1/4 : ℝ) := by nlinarith
  have hκ : 0<κ := flagDistortion_pos C.base (by change ε<1; linarith)
  have hbudget (i : ℕ) (hi : i<N) : relativeBudget C.base (C.increment i)=relativeBudget S.base (S.increment i) :=
    formMap_budget D S.base (S.increment i) hD h.original.1 (h.original.2.2.1 i hi).1
  have hsum : (∑ i∈range N, relativeBudget C.base (C.increment i))≤W := sum_le_sum fun i hi =>
    (hbudget i (mem_range.mp hi)).le.trans (h.original.2.2.1 i (mem_range.mp hi)).2
  have hvb : v≤2*((1+ε)/(1-ε))*W := by
    change 2*κ*(∑ i∈range N, relativeBudget C.base (C.increment i))≤2*κ*W
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  -- Apply the exact original slack only after deriving the true flag and displacement bounds.
  obtain ⟨heps,_,_,hv4,hv1,hθ,hθ₁,hθ₂⟩ := prequadratic_slack_controls N hN W ε v hW hε hεW hsmall hvb
  refine ⟨by change ε<1; linarith,hv1,?_,?_,?_,hv4⟩
  · intro i hi
    rw [hbudget i hi]
    exact (h.increment i hi).trans (mul_le_mul_of_nonneg_right hθ₁ (hω i hi))
  · have hc := formMap_budget D S.base S.terminal hD h.original.1 h.original.2.2.2.1
    change relativeBudget C.base C.terminal=relativeBudget S.base S.terminal at hc
    rw [hc]
    exact h.terminal.trans (mul_le_mul_of_nonneg_right hθ₂ hw)
  · have hsym : (S.base-A).IsSymm := h.original.1.1.isSymm.sub hA.1.isSymm
    have he : C.base-formMap D A=formMap D (S.base-A) := (map_sub (formMap D) S.base A).symm
    rw [he,formMap_budget D A (S.base-A) hD hA hsym]
    nlinarith [h.base_margin,mul_le_mul_of_nonneg_left hv4 (by linarith : 0≤1+r)]

end
end krylov.Information
