import jacobi.GelfandLevitan.Coercivity
import jacobi.GelfandLevitan.CutoffSpace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The complex Hilbert space uses the same Lebesgue interval as the real
construction. Real and imaginary parts preserve actual almost-everywhere
representatives and split its squared norm. Closed support subspaces are
the zero extensions of the physical spaces L2(0,t).
Use: contains all physical prefix spaces by zero extension in the complex GL inverse estimate.
-/
namespace jacobi.Analytic
noncomputable section
open Set MeasureTheory Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- The genuine complex L2 space on the shared unit interval.
Use: contains all physical prefix spaces by zero extension in the complex GL inverse estimate.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
abbrev ComplexL2 := Lp ℂ 2 (volume : Measure Interval)

/-- Real part of a complex L2 class, taken by the community quotient-compatible composition.
Use: transfers the original real quadratic lower bound to complex inputs.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: mathlib, ContinuousLinearMap.compLpL. -/
def realL2 : ComplexL2 →L[ℝ] Space := _root_.Complex.reCLM.compLpL 2 volume

/-- Imaginary part of a complex L2 class on the unchanged physical measure.
Use: supplies the second real quadratic form in complex coercivity.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: mathlib, ContinuousLinearMap.compLpL. -/
def imagL2 : ComplexL2 →L[ℝ] Space := _root_.Complex.imCLM.compLpL 2 volume

/-- The genuine L2 real-part representative agrees almost everywhere with pointwise real part.
Use: identifies real quadratic integrals without selecting special representatives of L2 classes.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: use the community representative theorem for composition by a continuous linear map. -/
theorem realL2_ae (v : ComplexL2) : realL2 v =ᵐ[volume] fun s => (v s).re :=
  _root_.Complex.reCLM.coeFn_compLpL v

/-- The genuine L2 imaginary-part representative agrees almost everywhere with pointwise imaginary part.
Use: identifies the imaginary quadratic contribution to the same complex GL form.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: apply the community quotient representative theorem to the imaginary-part map. -/
theorem imagL2_ae (v : ComplexL2) : imagL2 v =ᵐ[volume] fun s => (v s).im :=
  _root_.Complex.imCLM.coeFn_compLpL v

/-- Complex L2 squared norm is exactly the sum of the two genuine real L2 squared norms.
Use: preserves the original coercivity constant when passing from real to complex GL operators.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: the standard real and imaginary decomposition of complex L2.
Proof: write each norm as its actual integral inner product, commute real part with the complex integral, and use the two almost-everywhere representative identities. -/
theorem complexL2_norm_sq (v : ComplexL2) :
    ‖v‖^2=‖realL2 v‖^2+‖imagL2 v‖^2 := by
  -- The equality concerns the true quotient norms, not pointwise values of a selected class.
  have hn := congrArg _root_.Complex.re (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v)
  have hre := integral_re (L2.integrable_inner (𝕜 := ℂ) v v)
  change (∫ s:Interval,(inner ℂ (v s) (v s)).re)=
    (∫ s:Interval,inner ℂ (v s) (v s)).re at hre
  rw [L2.inner_def,← hre] at hn
  norm_cast at hn
  change (∫ s:Interval,(inner ℂ (v s) (v s)).re)=‖v‖^2 at hn
  rw [← real_inner_self_eq_norm_sq (realL2 v),← real_inner_self_eq_norm_sq (imagL2 v),L2.inner_def,L2.inner_def,
    ← integral_add (L2.integrable_inner (𝕜 := ℝ) (realL2 v) (realL2 v))
      (L2.integrable_inner (𝕜 := ℝ) (imagL2 v) (imagL2 v))]
  rw [← hn]
  apply integral_congr_ae
  filter_upwards [realL2_ae v,imagL2_ae v] with s hs hi
  rw [hs,hi]
  change ((v s)*star (v s)).re=(v s).re*(v s).re+(v s).im*(v s).im
  simp only [_root_.Complex.mul_re,_root_.Complex.star_def,_root_.Complex.conj_re,
    _root_.Complex.conj_im,mul_neg,sub_neg_eq_add]

/-- Actual complex restriction to the physical tail after t.
Use: its closed kernel realizes exactly the source domain L2(0,t) for the continued GL operator.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def complexRestriction (t : ℝ) : ComplexL2 →L[ℂ]
    Lp ℂ 2 ((volume : Measure Interval).restrict (outsideBefore t)) :=
  LpToLpRestrictCLM Interval ℂ ℂ volume 2 (outsideBefore t)

/-- The genuine complex physical prefix Hilbert space inside the fixed unit domain.
Use: the operator and its inverse below act on the actual source L2(0,t), including arbitrary measurable inputs.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def complexPrefix (t : ℝ) : Submodule ℂ ComplexL2 := (complexRestriction t).ker

/-- Membership in the complex physical prefix is the exact almost-everywhere tail support condition.
Use: applies the original real coercivity theorem to both parts of every complex prefix input.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: characterize the zero class of the actual restriction using its community representative theorem and measurable-tail restriction. -/
theorem mem_complexPrefix (t : ℝ) (v : ComplexL2) :
    v∈complexPrefix t ↔ ∀ᵐ s:Interval,t<(s:ℝ) → v s=0 := by
  -- Restriction and vanishing use the same original Lebesgue measure.
  change complexRestriction t v=0 ↔ _
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have he := LpToLpRestrictCLM_coeFn ℂ (outsideBefore t) v
  constructor
  · intro hz
    simpa only [outsideBefore,Set.mem_ofPred_eq,Pi.zero_apply] using
      (ae_restrict_iff' (outsideBefore_measurable t)).mp (he.symm.trans hz)
  · intro hv
    exact he.trans ((ae_restrict_iff' (outsideBefore_measurable t)).mpr hv)

/-- Every complex physical prefix is closed in the genuine ambient L2 space.
Use: obtains the complete Hilbert space and orthogonal projection used by the actual GL compression.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: it is the kernel of the actual bounded restriction map. -/
theorem complexPrefix_closed (t : ℝ) : IsClosed (complexPrefix t : Set ComplexL2) :=
  (complexRestriction t).isClosed_ker

/-- Each genuine complex prefix Hilbert space is complete.
Use: the community coercive-operator inverse theorem applies on the physical source interval.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the physical prefix is a proved closed subspace of complex L2. -/
instance complexPrefix_complete (t : ℝ) : CompleteSpace (complexPrefix t) :=
  (complexPrefix_closed t).completeSpace_coe

end
end jacobi.Analytic
