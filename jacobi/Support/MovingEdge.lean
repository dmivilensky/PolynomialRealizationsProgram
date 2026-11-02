import jacobi.Support.CorrectedEdge
import jacobi.GelfandLevitan.KernelTerm

/-!
Article: jacobi, Proposition C.3.
The genuine corrected support-polynomial edge limit is evaluated at
arbitrary moving physical half-chain indices and at the actual target
and support spectral nodes. The limits use the same real reference
solutions as the previously constructed original GL kernel terms.
Use: supportPolynomial_target_limit and supportPolynomial_model_limit give the original fixed-edge factors entering the target-minus-support Gram summands.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter Polynomial jacobi.Reference
open scoped Topology

/-- The actual corrected support polynomials have their genuine reference-solution limit at every moving physical half-chain index and every convergent actual corrected energy.
Use: supportPolynomial_target_limit and supportPolynomial_model_limit give the original fixed-edge factors entering the target-minus-support Gram summands.
Article: jacobi, Proposition C.3.
Proof: the proved full uniform polynomial edge limit makes the actual mesh error tend to zero. The genuine reference solution is continuous at the limiting physical point, including either endpoint of the closed half interval. Adding these two limits gives the asserted original polynomial limit. -/
theorem supportPolynomial_moving_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {x:ℕ→ℝ} {E t:ℝ} (hx:Tendsto (fun n:ℕ => 2*(jacobi.Jacobi.frequency a b (n+1))^2*(1-x n)) atTop (𝓝 E))
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop)
    (i:∀n:ℕ,Fin (ns n+1)) (hi:∀ᶠn:ℕ in atTop,2*(i n).val≤ns n+1)
    (ht:t∈Icc (0:ℝ) (1/2)) (hit:Tendsto (fun n:ℕ => ((i n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun n:ℕ => (ns n:ℝ)^(-gamma a)*(supportPolynomial a b ha hb (ns n) (i n)).eval (x (ns n))) atTop
      (𝓝 ((topConstant a b*π^gamma a)*realSolution a E t)) := by
  -- The uniform finite edge error vanishes along the chosen actual moving index.
  have he : Tendsto (fun n:ℕ => (ns n:ℝ)^(-gamma a)*(supportPolynomial a b ha hb (ns n) (i n)).eval (x (ns n))-
      (topConstant a b*π^gamma a)*realSolution a E (((i n).val:ℝ)/(ns n:ℝ))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := supportPolynomial_edge ha hb hx ε hε
    filter_upwards [hns.eventually_ge_atTop N,hi] with n hn hin
    simpa only [Real.dist_eq,sub_zero] using hN (ns n) hn (i n) hin
  have hv := ((jacobi.GelfandLevitan.realSolution_continuousAt ha E ht).tendsto.comp hit).const_mul
    (topConstant a b*π^gamma a)
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using he.add hv

/-- Every actual fixed target edge energy has its genuine squared-Bessel-zero limit in the original support frequency scale.
Use: supportPolynomial_target_limit applies the actual corrected support edge theorem at the original Jacobi roots used by the target matrix.
Article: jacobi, Proposition C.3.
Proof: multiply the already proved original cosine-distance limit by two and use the exact n+1 matrix dimension. -/
theorem targetNode_energy_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    Tendsto (fun n:ℕ => 2*(jacobi.Jacobi.frequency a b (n+1))^2*
      (1-cos (jacobi.Jacobi.finiteAngleAt a b ha hb (n+1) k))) atTop
      (𝓝 (jacobi.Bessel.sigma a ha k)) := by
  have h := ((jacobi.Jacobi.cosine_distance_tendsto ha hb k).const_mul 2).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,mul_assoc,mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using h

/-- The same original corrected support polynomials evaluated at a fixed actual target node have the genuine Bessel-energy reference limit along every moving half-chain index.
Use: gramSummandAt_limit obtains the target part of the original GL summand, with the actual target probability limit.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: apply the proved general moving corrected-polynomial limit to the actual target squared-distance limit. -/
theorem supportPolynomial_target_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop)
    (i:∀n:ℕ,Fin (ns n+1)) (hi:∀ᶠn:ℕ in atTop,2*(i n).val≤ns n+1)
    {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) (hit:Tendsto (fun n:ℕ => ((i n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun n:ℕ => (ns n:ℝ)^(-gamma a)*(supportPolynomial a b ha hb (ns n) (i n)).eval
      (cos (jacobi.Jacobi.finiteAngleAt a b ha hb (ns n+1) k))) atTop
      (𝓝 ((topConstant a b*π^gamma a)*realSolution a (jacobi.Bessel.sigma a ha k) t)) :=
  supportPolynomial_moving_limit ha hb (targetNode_energy_limit ha hb k) ns hns i hi ht hit

/-- The same original corrected support polynomials evaluated at a fixed original support node have the genuine reference-eigenvalue limit along every moving half-chain index.
Use: gramSummandAt_limit obtains the support part of the original GL summand, retaining the same original probability and reference normalization.
Article: jacobi, Proposition C.3.
Proof: apply the proved general moving corrected-polynomial limit to the independently proved actual support-node energy limit. -/
theorem supportPolynomial_model_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop)
    (i:∀n:ℕ,Fin (ns n+1)) (hi:∀ᶠn:ℕ in atTop,2*(i n).val≤ns n+1)
    {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) (hit:Tendsto (fun n:ℕ => ((i n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun n:ℕ => (ns n:ℝ)^(-gamma a)*(supportPolynomial a b ha hb (ns n) (i n)).eval
      (jacobi.Jacobi.modelNode a b (ns n+1) k)) atTop
      (𝓝 ((topConstant a b*π^gamma a)*realSolution a (eigenvalue a k) t)) :=
  supportPolynomial_moving_limit ha hb ((supportNode_limit ha hb k).comp (tendsto_add_atTop_nat 1)) ns hns i hi ht hit

end
end jacobi.Support
