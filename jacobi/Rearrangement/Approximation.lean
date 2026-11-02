import jacobi.Rearrangement.Regular
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Every nonnegative L1 density admits actual nonnegative compactly supported
Lipschitz approximations. Smooth L1 density from mathlib is followed by the
positive-part contraction; compact support and a global Lipschitz constant
place each approximant in the proved regular rearrangement domain.
Source: density of smooth compactly supported functions in Lp, in mathlib.
Use: connects the proved regular rearrangement theorem to the article's full finite-energy domain.
-/
namespace jacobi.Rearrangement
noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Every nonnegative L1 density has a regular nonnegative approximation with prescribed L1 error.
Use: connects the proved regular rearrangement theorem to the article's full finite-energy domain.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: approximate in L1 by a smooth compactly supported function, take its
positive part, and use contraction toward the nonnegative original density.
Smooth compact support gives a global Lipschitz constant and finite support and range bounds. -/
theorem exists_regular_l1_approx {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : ℝ →ᵇ ℝ) (R C : ℝ) (K : ℝ≥0),
      0 ≤ R ∧ f ∈ regularFamily R C K ∧ (∫ x, |m x-f x|) ≤ ε := by
  -- Smooth density is supplied by the community library; positivity is restored by a pointwise contraction.
  obtain ⟨g,hgs,hgd,herr⟩ := (memLp_one_iff_integrable.mpr hm).exist_eLpNorm_sub_le
    ENNReal.one_ne_top (le_refl 1) hε
  have hgi : Integrable g := hgd.continuous.integrable_of_hasCompactSupport hgs
  have he : (∫ x, |m x-g x|) ≤ ε := by
    rw [(memLp_one_iff_integrable.mpr (hm.sub hgi)).eLpNorm_eq_integral_rpow_norm
      one_ne_zero ENNReal.one_ne_top] at herr
    simpa only [ENNReal.toReal_one,inv_one,Real.rpow_one,Real.norm_eq_abs,Pi.sub_apply,
      ENNReal.ofReal_le_ofReal_iff hε.le] using herr
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgs hgd (by simp)
  let v (x : ℝ) := max (g x) 0
  have hv : LipschitzWith K v := hK.max_const 0
  have hvs : HasCompactSupport v := hgs.comp_left (g := fun y : ℝ => max y 0) (max_self 0)
  obtain ⟨C,hC⟩ := hvs.exists_bound_of_continuous hv.continuous
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨v,hv.continuous⟩ (2*C) (by
    intro x y
    calc
      dist (v x) (v y) ≤ ‖v x‖+‖v y‖ := dist_le_norm_add_norm _ _
      _ ≤ C+C := add_le_add (hC x) (hC y)
      _ = 2*C := by ring)
  -- A support radius strictly larger than the compact support also ensures vanishing at its endpoints.
  obtain ⟨R,hR,hsR⟩ := hvs.isCompact.isBounded.subset_ball_lt 0 (0 : ℝ)
  have hreg : f ∈ regularFamily R C K := by
    refine ⟨hv,fun x => ⟨le_max_right _ _,?_⟩,fun x hx => ?_⟩
    · exact (le_abs_self (v x)).trans (hC x)
    · by_contra h
      have hb := hsR (subset_tsupport v h)
      rw [mem_ball,Real.dist_eq,sub_zero] at hb
      exact (not_lt_of_ge hx) hb
  refine ⟨f,R,C,K,hR.le,hreg,?_⟩
  apply le_trans (integral_mono (hm.sub (regularDensity f hreg).integrable).abs
    (hm.sub hgi).abs (fun x => ?_)) he
  change |m x-max (g x) 0| ≤ |m x-g x|
  have hx := hn x
  grind [abs_eq_max_neg]

end
end jacobi.Rearrangement
