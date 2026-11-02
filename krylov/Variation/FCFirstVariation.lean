import krylov.Stability.FCDomains
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Article: main_krylov, thm:A, first variation of the actual adaptive FC cycle.
Use: differentiate the real executed residual staircase with its genuine
quadratic model/search domains discharged, showing cancellation of all step derivatives.
Source: actual FC staircase, true static termination and the product rule.
-/

namespace krylov.Variation
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Stability
open scoped BigOperators InnerProductSpace
variable {n : ℕ}

/-- The true antisymmetric secant pairing equals its physical symmetric-operator difference pairing.
Use: the exact FC staircase contains an explicit vanishing operator factor at a quadratic reference.
Article: main_krylov, thm:A, differentiated commutator staircase.
Proof: transfer the older symmetric operator between the inner-product arguments. -/
theorem inner_operator_defect {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (s t : E) :
    inner ℝ s (B t)-inner ℝ t (A s)=inner ℝ s ((B-A) t) := by
  have he := hA s t
  change inner ℝ (A s) t=inner ℝ s (A t) at he
  rw [_root_.sub_apply,inner_sub_right,← he,real_inner_comm t]

/-- The actual terminal adaptive FC derivative satisfies the exact reference-step response coordinates.
Use: identifies the real trajectory's first variation and proves that derivatives of the adaptive steps cancel from the terminal response.
Article: main_krylov, thm:A, δg_n in actual CG step coordinates.
Proof: the actual FC cycle is analytic on its genuine open quadratic
domain. Differentiate its exact staircase after writing each defect with the explicit operator difference; that difference and the terminal gradient vanish at the reference, so all adaptive step-derivative terms vanish. -/
theorem fullFC_firstVariation_coordinates
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n))
    (hA : ∀ k, AnalyticAt ℝ (fun t => A t k) 0)
    (hD : ∀ k, HasDerivAt (fun t => A t k) (D k) 0)
    (hsym : ∀ t k, (A t k).toLinearMap.IsSymmetric)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA0 : A 0=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (hpre : ∀ k<N, CG.gradient Q g k≠0) (hstop : CG.gradient Q g N=0)
    {i : ℕ} (hi : i<N) :
    inner ℝ (referenceStep Q g i) (deriv (fun t => fcGradient fullMemory (A t) g N) 0)=
      ∑ j∈Finset.Ico (i+1) N, inner ℝ (referenceStep Q g i) ((D j-D i) (referenceStep Q g j)) := by
  -- Analyticity and the common real solve domain are derived from the actually executed quadratic reference.
  have ht := quadraticFC_prefix_analytic A (fun _ => g) 0 hA analyticAt_const Q hA0 hQ hpos N hpre
  have hdomain := quadraticFC_domains A (fun _ => g) 0 hA analyticAt_const Q hA0 hQ hpos N hpre
  let S := fun t k => fcStep fullMemory (A t) g k
  let G := fun t => fcGradient fullMemory (A t) g N
  have hG : HasDerivAt G (deriv G 0) 0 := ht.1.differentiableAt.hasDerivAt
  have hSi : HasDerivAt (fun t => S t i) (deriv (fun t => S t i) 0) 0 :=
    (ht.2 i hi).2.differentiableAt.hasDerivAt
  have hG0 : G 0=0 := by
    change fcGradient fullMemory (A 0) g N=0
    rw [hA0,(fullFC_reference_step Q hQ hpos g N).1,hstop]
  have hS0 (k : ℕ) : S 0 k=referenceStep Q g k := by
    change fcStep fullMemory (A 0) g k=_
    rw [hA0,(fullFC_reference_step Q hQ hpos g k).2.2]
  have hleft := hSi.inner ℝ hG
  simp only [hS0,hG0,inner_zero_right,add_zero] at hleft
  have hterm (j : ℕ) (hj : j∈Finset.Ico (i+1) N) :
      HasDerivAt (fun t => inner ℝ (S t i) ((A t j-A t i) (S t j)))
        (inner ℝ (referenceStep Q g i) ((D j-D i) (referenceStep Q g j))) 0 := by
    have hSj : HasDerivAt (fun t => S t j) (deriv (fun t => S t j) 0) 0 :=
      (ht.2 j (Finset.mem_Ico.mp hj).2).2.differentiableAt.hasDerivAt
    have hh := hSi.inner ℝ (((hD j).sub (hD i)).clm_apply hSj)
    simpa only [Pi.sub_apply,hA0,sub_self,_root_.zero_apply,add_zero,inner_zero_right,hS0] using hh
  have hright := HasDerivAt.fun_sum hterm
  have heq : (fun t => inner ℝ (S t i) (G t))=ᶠ[𝓝 (0 : ℝ)]
      (fun t => ∑ j∈Finset.Ico (i+1) N, inner ℝ (S t i) ((A t j-A t i) (S t j))) := by
    filter_upwards [hdomain] with t ht'
    have hs := fullFC_staircase (A t) g N (fun k hk => (ht' k hk).1) (fun k hk => (ht' k hk).2) hi
    refine hs.trans (Finset.sum_congr rfl (fun j _ => ?_))
    exact inner_operator_defect (A t i) (A t j) (hsym t i) (S t i) (S t j)
  exact hleft.unique (hright.congr_of_eventuallyEq heq)

end
end krylov.Variation
