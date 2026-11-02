import krylov.Variation.FCFirstVariation
set_option autoImplicit false
/-!
Article: main_krylov, apB:eq:nu and cor:lm, actual pre-exhaustion FC residual variation.
Use: differentiate the exact real full-memory FC staircase before
exhaustion, retaining the actual recorded-step/returned-gradient residual
rather than imposing a genuinely zero terminal reference gradient.
Source: the proved actual executed FC staircase, genuine open reference
solve/search domains and the true vanishing reference operator difference.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Stability krylov.Variation
open scoped BigOperators InnerProductSpace
variable {n : ℕ}
/-- The true observed residual derivative of an actually executed full-memory FC prefix is exactly its genuine triangular reference-step operator-difference response, before or at exhaustion.
Use: The true observed residual derivative of an actually executed full-memory FC prefix is exactly its genuine triangular reference-step operator-difference response, before or at exhaustion.
Article: main_krylov, apB:eq:nu and cor:lm, actual pre-exhaustion FC residual variation.
Proof: Use genuine actual analytic trajectory domains to apply the exact executed staircase in a real neighborhood. Each real antisymmetric defect contains an actual operator difference that vanishes at the true quadratic reference, so genuine adaptive step derivatives cancel. Differentiate the true finite sum and transfer its actual local residual identity. -/
theorem fullFC_residual_firstVariation
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n))
    (hA : ∀ k, AnalyticAt ℝ (fun t => A t k) 0)
    (hD : ∀ k, HasDerivAt (fun t => A t k) (D k) 0)
    (hsym : ∀ t k, (A t k).toLinearMap.IsSymmetric)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA0 : A 0=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (hpre : ∀ k<N, CG.gradient Q g k≠0)
    {i : ℕ} (hi : i<N) :
    deriv (fun t => inner ℝ (fcStep fullMemory (A t) g i) (fcGradient fullMemory (A t) g N)) 0=
      ∑ j∈Finset.Ico (i+1) N, inner ℝ (referenceStep Q g i) ((D j-D i) (referenceStep Q g j)) := by
  -- Analyticity and the common real solve domain are derived from the actually executed quadratic reference.
  have ht := quadraticFC_prefix_analytic A (fun _ => g) 0 hA analyticAt_const Q hA0 hQ hpos N hpre
  have hdomain := quadraticFC_domains A (fun _ => g) 0 hA analyticAt_const Q hA0 hQ hpos N hpre
  let S := fun t k => fcStep fullMemory (A t) g k
  let G := fun t => fcGradient fullMemory (A t) g N
  have hSi : HasDerivAt (fun t => S t i) (deriv (fun t => S t i) 0) 0 :=
    (ht.2 i hi).2.differentiableAt.hasDerivAt
  have hS0 (k : ℕ) : S 0 k=referenceStep Q g k := by
    change fcStep fullMemory (A 0) g k=_
    rw [hA0,(fullFC_reference_step Q hQ hpos g k).2.2]
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
  rw [heq.deriv_eq]
  exact hright.deriv

end
end krylov.Envelope
