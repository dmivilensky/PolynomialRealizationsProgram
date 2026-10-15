import «2610.05164v2».Calibration.ChainRule
import Mathlib.Analysis.Calculus.TangentCone.DimOne
import Mathlib.Topology.Order.LeftRightNhds

/-!
Article: 2610.05164v2, Proposition 8.
Locality on level sets; no monotonicity of the coordinate is assumed.
Use: `«2610.05164v2».Residual.finite_exception_chain_rule` feeds
`«2610.05164v2».Residual.Price.chain_rule` (chain rule).
Proof chain: `«2610.05164v2».Calibration.Data.energy_ge_spectral_bound` — 2610.05164v2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace «2610.05164v2».Residual
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, f x=c → ∀ d : ℝ,
HasDerivAt f d x → d=0`.

Use: `«2610.05164v2».Residual.finite_exception_chain_rule` uses this identity to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x => φ (q
x)) (w (q x)*d x) x`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem derivative_zero_on_level_ae (f : ℝ → ℝ) (c : ℝ) :
    ∀ᵐ x, f x=c → ∀ d : ℝ, HasDerivAt f d x → d=0 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let s : Set ℝ := {x | f x=c}
  have hc := (countable_setOfPred_isolated_right_within (s := s)).measure_zero volume
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hc] with x hx hxc d hd
  have hn : NeBot (𝓝[s ∩ Ioi x] x) := by
    apply Filter.neBot_iff.mpr
    exact fun h => hx ⟨hxc,h⟩
  have ha : AccPt x (𝓟 s) := by
    rw [accPt_principal_iff_nhdsWithin]
    apply hn.mono (nhdsWithin_mono x ?_)
    intro y hy
    exact ⟨hy.1,by simp only [mem_singleton_iff]; exact ne_of_gt hy.2⟩
  have hu := ha.uniqueDiffWithinAt
  have h0 : HasDerivWithinAt f 0 s x := by
    apply (hasDerivWithinAt_const x s c).congr
    · exact fun _ hy => hy
    · exact hxc
  exact (hd.hasDerivWithinAt.derivWithin hu).symm.trans (h0.derivWithin hu)

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, DifferentiableAt ℝ f x`.

Use: `«2610.05164v2».Residual.finite_exception_chain_rule` uses this assertion to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x => φ (q
x)) (w (q x)*d x) x`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem locallyAC_ae_differentiable {f : ℝ → ℝ}
    (hf : ∀ a b, AbsolutelyContinuousOnInterval f a b) : ∀ᵐ x, DifferentiableAt ℝ f x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hn : ∀ n : ℕ, ∀ᵐ x, x ∈ uIcc (-(n:ℝ)) n → DifferentiableAt ℝ f x :=
    fun n => (hf (-(n:ℝ)) n).ae_differentiableAt
  filter_upwards [ae_all_iff.mpr hn] with x hx
  obtain ⟨n,hn⟩ := exists_nat_gt |x|
  exact hx n (by
    rw [uIcc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) n] : -(n:ℝ) ≤ n)]
    exact ⟨by linarith [neg_abs_le x],by linarith [le_abs_self x]⟩)

/--
A Lipschitz primitive may fail to be differentiable at finitely many prices. Both the
coordinate and its composition have derivative zero on those level sets almost everywhere.

Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x => φ (q
x)) (w (q x)*d x) x`.

Use: `«2610.05164v2».Residual.Price.chain_rule` uses this identity to establish establishes the
stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x => P.antiderivative (q
x)) (P.value (q x)*d x) x`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `q x ∈ D` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem finite_exception_chain_rule {q d φ w : ℝ → ℝ} {K : NNReal}
    (hq : ∀ a b, AbsolutelyContinuousOnInterval q a b)
    (hd : ∀ᵐ x, HasDerivAt q (d x) x) (hφ : LipschitzWith K φ)
    (D : Finset ℝ) (hregular : ∀ y ∉ D, HasDerivAt φ (w y) y) :
    ∀ᵐ x, HasDerivAt (fun x => φ (q x)) (w (q x)*d x) x := by
  -- Separate `q x ∈ D` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  have hac (a b : ℝ) : AbsolutelyContinuousOnInterval (fun x => φ (q x)) a b :=
    hφ.comp_absolutelyContinuousOnInterval (hq a b)
  have hlevels : ∀ c : D, ∀ᵐ x,
      (q x=(c:ℝ) → ∀ e, HasDerivAt q e x → e=0) ∧
      (φ (q x)=φ c → ∀ e, HasDerivAt (fun x => φ (q x)) e x → e=0) := by
    intro c
    exact (derivative_zero_on_level_ae q c).and
      (derivative_zero_on_level_ae (fun x => φ (q x)) (φ c))
  filter_upwards [hd,locallyAC_ae_differentiable hac,ae_all_iff.mpr hlevels] with x hx hdiff hlev
  by_cases hi : q x ∈ D
  · have hc := hlev ⟨q x,hi⟩
    have hd0 := hc.1 rfl _ hx
    have he0 := hc.2 rfl _ hdiff.hasDerivAt
    simpa only [hd0,mul_zero,he0] using hdiff.hasDerivAt
  · exact (hregular (q x) hi).comp x hx

end
end «2610.05164v2».Residual
