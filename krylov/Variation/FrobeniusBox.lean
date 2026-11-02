import krylov.Variation.FrobeniusResponse
import krylov.Variation.FCLocalRemainder

/-!
Article: main_krylov, thm:C2(a), sharp actual FC independent Frobenius budgets.
Use: the genuine executed FC derivative has exactly the printed symmetric
backward-error factor 1/√2 for every independent source budget profile.
Source: BunchEtAl89; reuse the actual symmetric cross-block cost, computed
CG tails, globally analytic canonical FC path and its true derivative.
-/

namespace krylov.Variation
noncomputable section
open Matrix Finset Filter Asymptotics Topology krylov.Reference krylov.Secant
  krylov.Methods krylov.LinearAlgebra chebyshev1
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true spatial CG response has the sharp independent Frobenius box-budget upper bound.
Use: retain the genuine symmetric √2 gain separately on every original source increment.
Article: main_krylov, thm:C2(a), FC coefficient Σω_l‖e_(l+1)‖/√2.
Proof: sum the actual sharp symmetric cross-action costs on the computed
orthogonal CG flags, apply each original independent Frobenius budget and
divide by the strictly positive square root of two.
-/
theorem frobenius_box_response_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (I : Finset ℕ)
    (hI : ∀ l∈I, l+1<referenceAtomCount A hA g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l∈I, (E l).IsSymm)
    (ω : ℕ → ℝ) (hω : ∀ l∈I, hsNorm (E l)≤ω l) :
    ‖fullCycleResponse A g I E‖≤(∑ l∈I, ω l*‖cgCanonicalError A g (l+1)‖)/Real.sqrt 2 := by
  -- The actual matrix symmetry pays the √2 cost before aggregating the primitive budgets.
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2))).mpr
  have ht := mul_le_mul_of_nonneg_left (norm_sum_le I
    (fun l => (oldFlag A g l).starProjection (cgOperator (E l) (remainingTail A g l)))) (Real.sqrt_nonneg 2)
  rw [mul_sum] at ht
  have ht' : ‖fullCycleResponse A g I E‖*Real.sqrt 2≤∑ l∈I, Real.sqrt 2*
      ‖(oldFlag A g l).starProjection (cgOperator (E l) (remainingTail A g l))‖ := by
    simpa only [fullCycleResponse,cgOperator,mul_comm] using ht
  apply ht'.trans
  apply sum_le_sum
  intro l hl
  exact (response_hs_cross A hA g l (hI l hl) (E l) (hE l hl)).trans
    (by simpa only [remainingTail_norm] using mul_le_mul_of_nonneg_right (hω l hl) (norm_nonneg (remainingTail A g l)))

/-- Actual symmetric finite increments attain the independent Frobenius box response bound on every genuine preterminal profile.
Use: the printed FC coefficient is attained by actual source matrices with every individual budget, including empty or zero profiles.
Article: main_krylov, thm:C2(a), attaining symmetric backward-error family.
Proof: each true remaining-tail cross matrix is scaled by its own budget
and 1/√2. Its twice-counted Frobenius energy is exactly that budget squared.
All genuine projected tail actions point along the same first CG unit step,
so the norm triangle inequality is an equality for the whole source profile.
-/
theorem frobenius_box_response_attained (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : 0<referenceAtomCount A hA g)
    (I : Finset ℕ) (hI : ∀ l∈I, l+1<referenceAtomCount A hA g)
    (ω : ℕ → ℝ) (hω : ∀ l∈I, 0≤ω l) :
    ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ, (∀ l, (E l).IsSymm) ∧
      (∀ l∈I, hsNorm (E l)=ω l) ∧
      ‖fullCycleResponse A g I E‖=(∑ l∈I, ω l*‖cgCanonicalError A g (l+1)‖)/Real.sqrt 2 := by
  -- Use exactly the actual reference tail in every attaining planar increment.
  let e := canonicalCGUnitStep A g 0
  let E := fun l => planarMatrix e (NormedSpace.normalize (remainingTail A g l)) 0 (ω l/Real.sqrt 2) 0
  have hr : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : (Real.sqrt 2)^2=(2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hp (l : ℕ) (hl : l∈I) := response_cross_increment A hA g l (hI l hl)
    (ω l/Real.sqrt 2) (div_nonneg (hω l hl) hr.le)
  refine ⟨E,fun _ => planarMatrix_isSymm _ _ _ _ _,?_,?_⟩
  · intro l hl
    have hs := hsNorm_sq (E l)
    rw [(hp l hl).2.2.1] at hs
    have he : 2*(ω l/Real.sqrt 2)^2=(ω l)^2 := by rw [div_pow,hr2]; ring
    rw [he] at hs
    nlinarith [hsNorm_nonneg (E l),hω l hl]
  · have hv : fullCycleResponse A g I E=
        ((∑ l∈I, ω l*‖cgCanonicalError A g (l+1)‖)/Real.sqrt 2) • e := by
      unfold fullCycleResponse
      rw [Finset.sum_div,sum_smul]
      exact sum_congr rfl fun l hl => by
        have ht := (hp l hl).2.2.2
        simpa only [remainingTail_norm,div_mul_eq_mul_div] using ht
    rw [hv,norm_smul,Real.norm_eq_abs,(firstStep_common A hA g hcount).1,mul_one,
      abs_of_nonneg (div_nonneg (sum_nonneg fun l hl => mul_nonneg (hω l hl) (norm_nonneg _)) hr.le)]

/-- The final true CG response tail vanishes exactly, so a full terminal response equals its preterminal increment sum.
Use: connect the sharp source increment coefficient to the actual n-iteration FC derivative at the true source indices.
Article: main_krylov, thm:C2(a), exact terminal zero response term.
Proof: actual CG terminates at its full active count. The genuine last
remaining tail is therefore zero, and so is its projected increment action.
-/
theorem fullCycleResponse_drop_last {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount A hA g=N+1)
    (E : ℕ → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    fullCycleResponse A g (range (N+1)) E=fullCycleResponse A g (range N) E := by
  have ht : remainingTail A g N=0 := by
    simp only [remainingTail,cgCanonicalError,show CG.gradient (cgOperator A) g (N+1)=0 by
      simpa only [hcount] using cg_terminates A hA g,map_zero,neg_zero]
  simp only [fullCycleResponse,sum_range_succ,ht,map_zero,add_zero]

/-- The actual executed FC derivative has the sharp attained independent Frobenius coefficient for every original profile.
Use: the norm variant is proved for the genuine adaptive output, not only its spatial response candidate.
Article: main_krylov, thm:C2(a), complete sharp first-order FC statement.
Proof: the real canonical perturbation path has the proved actual FC
response derivative. Its terminal response term is exactly zero. The sharp
independent Frobenius response bound and actual symmetric attaining family
therefore give the greatest derivative norm in the genuine source class.
-/
theorem canonicalFC_frobenius_box_sharp {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount A hA g=N+1)
    (ω : ℕ → ℝ) (hω : ∀ l<N, 0≤ω l) :
    IsGreatest {v : ℝ | ∃ E : ℕ → Matrix (Fin (N+1)) (Fin (N+1)) ℝ,
      (∀ l, (E l).IsSymm) ∧ (∀ l<N, hsNorm (E l)≤ω l) ∧
      v=‖deriv (fun t => cgOperator (metricRoot A)⁻¹
        (fcGradient fullMemory (canonicalFCPath A E t) g (N+1))) 0‖}
      ((∑ l∈range N, ω l*‖cgCanonicalError A g (l+1)‖)/Real.sqrt 2) := by
  -- The genuine actual derivative and the original n−1 source increments have exactly matching indices.
  have hpre (l : ℕ) (hl : l∈range N) : l+1<referenceAtomCount A hA g := by
    have := mem_range.mp hl
    omega
  obtain ⟨E,hE,hbudget,hatt⟩ := frobenius_box_response_attained A hA g (by omega) (range N) hpre
    ω (fun l hl => hω l (mem_range.mp hl))
  constructor
  · refine ⟨E,hE,fun l hl => (hbudget l (mem_range.mpr hl)).le,?_⟩
    dsimp only [cgOperator]
    rw [(canonicalFC_response_hasDerivAt A hA g hcount E hE).deriv,fullCycleResponse_drop_last A hA g hcount]
    exact hatt.symm
  · rintro v ⟨F,hF,hFb,rfl⟩
    dsimp only [cgOperator]
    rw [(canonicalFC_response_hasDerivAt A hA g hcount F hF).deriv,fullCycleResponse_drop_last A hA g hcount]
    exact frobenius_box_response_le A hA g (range N) hpre F (fun l _ => hF l) ω
      (fun l hl => hFb l (mem_range.mp hl))

end
end krylov.Variation
