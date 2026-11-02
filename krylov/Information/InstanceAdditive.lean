import krylov.Information.PreQuadraticInstance
import krylov.Information.AdmissibleUpper

/-!
Article: main_krylov, s4:cor-Q, original additive cubic instance comparison.
Use: combine the true original multiplicative instance inequality with
the genuine all-source sharp RFC upper bound on one common source tube.
Source: actual compact uniform reference and source bounds, original
pre-quadratic twin geometry and nonnegative real cubic-loss algebra.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

set_option maxHeartbeats 600000 in
/-- The actual common pre-quadratic admissible twin gives the original additive cubic instance bound for every genuine one-correction CG-consistent method, with constants fixed before every source profile and scenario.
Use: complete the printed additive form of the original pre-quadratic instance-optimality corollary.
Article: main_krylov, s4:cor-Q, max(ρ_M(Ξ),ρ_M(Ξ♯)) ≥ ρ_RFC(Ξ)−Cω³.
Proof: choose the genuine original compact instance and sharp all-source RFC upper constants first. A common maximal-budget tube enforces the stated primitive smallness domains. The true RFC risk is uniformly quadratic, and the actual multiplicative instance loss has order one in that same maximal budget. Their product gives the uniform actual cubic additive loss. -/
theorem preQuadratic_instance_additive
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcountA : referenceAtomCount A hA g=N+1) (hN : 0<N) :
    ∃ r₀ δ C : ℝ, 0<r₀ ∧ 0<δ ∧ 0<C ∧ ∀ (r : ℝ), 0≤r → r≤r₀ →
      ∀ (ω : ℕ → ℝ) (w τ μ : ℝ), 0≤w → 0≤τ → 0≤μ → μ≤δ →
        (∀ i<N, ω i≤μ) → w≤μ → τ≤μ →
      ∀ S : Scenario (N+1), S.NaturalInner A r ω w τ →
      ∀ (Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hQ : Q.PosDef),
        referenceAtomCount Q hQ g=N+1 → S.PreQuadratic (cgOperator Q) g N →
      ∀ m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))), CGConsistent m → OneCorrectionMethod m →
        S.outputRatio (rfcMethod fullMemory 1) g N-C*μ^3≤
          max (S.outputRatio m g N) ((S.preQuadraticTwin Q g).outputRatio m g N) := by
  -- Fix the actual instance and sharp physical RFC upper constants before all scenarios and competitors.
  obtain ⟨rI,L,hrI,_,hL,hinstance⟩ := preQuadratic_instance A hA g hcountA hN
  obtain ⟨rU,δU,CU,hrU,hδU,hCU,hupper⟩ := admissible_rfc_sharp_upper A hA g hN hcountA
  let b : ℝ := (N : ℝ)+1
  have hb : 0<b := by dsimp only [b]; positivity
  let r₀ := min rI rU
  let δ := min δU (min 1 (min (1/(6*b)) (1/(4*b^2))))
  let a := b*(6+4*(1+r₀)*L)
  let B := b^2+CU
  let C := a*B
  have hr₀ : 0<r₀ := lt_min hrI hrU
  have hδ : 0<δ := by dsimp only [δ]; positivity
  have ha : 0<a := by dsimp only [a]; positivity
  have hB : 0<B := by dsimp only [B]; positivity
  refine ⟨r₀,δ,C,hr₀,hδ,mul_pos ha hB,?_⟩
  intro r hr hrr ω w τ μ hw hτ hμ hμδ hω hwμ hτμ S h Q hQ hcountQ hpre m hm h1
  let W := ∑ i∈range N, ω i
  let R := S.outputRatio (rfcMethod fullMemory 1) g N
  have hW : 0≤W := sum_nonneg fun i hi =>
    (norm_nonneg (relativeOperator S.base (S.increment i))).trans (h.original.2.2.1 i (mem_range.mp hi)).2
  have hWμ : W≤(N : ℝ)*μ := by simpa using sum_le_sum (s := range N) (g := fun _ => μ) (fun i hi => hω i (mem_range.mp hi))
  have hWb : W≤b*μ := by dsimp only [b]; nlinarith
  have hs : W+w≤b*μ := by dsimp only [b]; nlinarith
  have hμU : μ≤δU := hμδ.trans (min_le_left _ _)
  have hμ₁ : μ≤1 := hμδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hμ6 : μ≤1/(6*b) := hμδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hμ4 : μ≤1/(4*b^2) := hμδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsmall : 4*((N : ℝ)+1)*W≤1 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*b^2)).mp hμ4
    change 4*b*W≤1
    nlinarith [mul_le_mul_of_nonneg_left hWb (by positivity : 0≤4*b)]
  have hμsmall : 6*((N : ℝ)+1)*μ≤1 := by
    have hh := (le_div_iff₀ (by positivity : 0<6*b)).mp hμ6
    change 6*b*μ≤1
    nlinarith
  have hKs : sharpConstant W w≤(W+w)^2 := (sharpConstant_upper hW hw).trans (by nlinarith)
  have hKU : sharpConstant W w≤b^2*μ^2 := hKs.trans (by simpa only [mul_pow] using pow_le_pow_left₀ (add_nonneg hW hw) hs 2)
  have hcube : μ^3≤μ^2 := by nlinarith [mul_le_mul_of_nonneg_left hμ₁ (sq_nonneg μ)]
  have hRU : R≤B*μ^2 := by
    have he := hupper r (hrr.trans (min_le_right _ _)) ω w τ μ hμ hμU hω hwμ hτμ S h.original
    dsimp only [R,B]
    nlinarith [mul_le_mul_of_nonneg_left hcube hCU.le]
  have hR : 0≤R := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hi := hinstance r hr (hrr.trans (min_le_left _ _)) ω w τ μ hw hτ hμ hω hwμ hsmall hμsmall S h
    Q hQ hcountQ hpre m hm h1
  have hcoef : ((N : ℝ)+1)*(6+4*(1+r)*L)≤a := by
    dsimp only [a,b]
    nlinarith [mul_le_mul_of_nonneg_left hrr (by positivity : 0≤4*((N : ℝ)+1)*L)]
  have hI : (1-a*μ)*R≤max (S.outputRatio m g N) ((S.preQuadraticTwin Q g).outputRatio m g N) := by
    exact (mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hcoef hμ]) hR).trans hi
  have hprod := mul_le_mul_of_nonneg_left hRU (mul_nonneg ha.le hμ)
  change R-C*μ^3≤_
  dsimp only [C]
  nlinarith

end
end krylov.Information
