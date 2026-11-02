import krylov.OneGradient.TwoQueryMinimaxLoss
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), original physical all-M1 asymptotic minimax.
Use: identify the actual sharp coefficient on the complete known-base
source class, allowing a different arbitrary M1 policy at each budget.
Source: uniform finite physical lower bound, one real centring algorithm
with a common cubic upper loss, and genuine real filter limits.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference
open Filter Topology

/-- An original source-wide asymptotic second-order guarantee along a
shrinking positive budget sequence. The remainder is independent of the
unknown physical scenario and vanishes after true scale-squared division.
Use: the method may change arbitrarily at each scale before the source
matrices are chosen; no policy limit or continuity is required.
Article: main_krylov, thm:local(c), genuine limiting M1 guarantee. -/
def knownBaseTwoQueryAsymptoticGuarantee
    (base : Matrix (Fin 2) (Fin 2) ℝ) (g : EuclideanSpace ℝ (Fin 2))
    (W w : ℝ) (scale : ℕ → ℝ)
    (method : ℕ → OneGradientMethod (EuclideanSpace ℝ (Fin 2))) (v : ℝ) : Prop :=
  ∃ remainder : ℕ → ℝ,
    Tendsto (fun j => remainder j/(scale j)^2) atTop (𝓝 0) ∧
      ∀ᶠ j in atTop,knownBaseTwoQueryGuarantee base g (W*scale j) (w*scale j)
        (method j) (v*(scale j)^2+remainder j)

/-- Every genuine source-wide limiting coefficient of arbitrary actual
M1 methods is at least V2, even with changing or discontinuous policies.
Use: the full original physical minimax lower bound is independent of
CG consistency, bounded queries, bounded outputs or finite-risk premises.
Article: main_krylov, thm:local(c), original asymptotic all-method lower bound.
Proof: each genuine finite physical guarantee obeys the normalized
four-adversary lower estimate. Its actual common loss tends to one and
the genuine remainder divided by scale squared tends to zero. Pass the
true eventual inequality through these real limits. -/
theorem knownBaseTwoQuery_asymptotic_lower
    (base : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin 2)) (hc : referenceAtomCount base hb g=2)
    (W w v : ℝ) (hW : 0< W) (hw : 0< w) (scale : ℕ → ℝ)
    (hscale : ∀ j,0< scale j) (hzero : Tendsto scale atTop (𝓝 0))
    (method : ℕ → OneGradientMethod (EuclideanSpace ℝ (Fin 2)))
    (hm : ∀ j,OneGradientSpanRestricted (method j))
    (hguarantee : knownBaseTwoQueryAsymptoticGuarantee base g W w scale method v) :
    twoDimensionalValue W w≤ v := by
  obtain ⟨remainder,hrem,hbound⟩ := hguarantee
  have hlower : ∀ᶠ j in atTop,twoDimensionalValue W w≤
      twoQueryMinimaxLoss W w (scale j)*(v+remainder j/(scale j)^2) := by
    filter_upwards [hbound] with j hj
    apply knownBaseTwoQueryGuarantee_normalized_lower base hb g hc W w (scale j)
      (v+remainder j/(scale j)^2) hW hw (hscale j) (method j) (hm j)
    have he : (v+remainder j/(scale j)^2)*(scale j)^2=v*(scale j)^2+remainder j := by
      field_simp [(hscale j).ne']
    rwa [he]
  have hconv : Tendsto (fun j => twoQueryMinimaxLoss W w (scale j)*(v+remainder j/(scale j)^2))
      atTop (𝓝 v) := by
    simpa only [add_zero,one_mul] using
      (twoQueryMinimaxLoss_tendsto W w scale hzero).mul ((tendsto_const_nhds (x := v)).add hrem)
  exact ge_of_tendsto hconv hlower

/-- The actual history-only known-base centring method attains V2 on
the full original physical source class along every shrinking positive
budget sequence, with a genuine common cubic remainder.
Use: a real source-admissible M1 policy, fixed before every unknown matrix,
attains the original asymptotic minimax coefficient using three gradients.
Article: main_krylov, thm:local(c), original attaining algorithm.
Proof: its finite physical all-scenario upper bound has remainder
2W²(W+w) scale³. Exact positive-scale cancellation makes the normalized
remainder a fixed constant times scale. Smallness is eventual by its true limit. -/
theorem knownBaseCentredMethod_asymptotic_guarantee
    (base : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin 2)) (hc : referenceAtomCount base hb g=2)
    (W w : ℝ) (hW : 0< W) (hw : 0≤ w) (scale : ℕ → ℝ)
    (hscale : ∀ j,0< scale j) (hzero : Tendsto scale atTop (𝓝 0)) :
    knownBaseTwoQueryAsymptoticGuarantee base g W w scale
      (fun j => knownBaseCentredMethod base (W*scale j)) (twoDimensionalValue W w) := by
  let C := 2*W^2*(W+w)
  refine ⟨fun j => C*(scale j)^3,?_,?_⟩
  · have he (j : ℕ) : C*(scale j)^3/(scale j)^2=C*scale j := by field_simp [(hscale j).ne']
    simp_rw [he]
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hzero
  · have hsmall : ∀ᶠ j in atTop,W*scale j≤(1/2 : ℝ) := by
      have ht : Tendsto (fun j => W*scale j) atTop (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_const_nhds (x := W)).mul hzero
      exact (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))).mono (fun _ h => h.le)
    filter_upwards [hsmall] with j hj
    exact knownBaseCentredMethod_twoQueryGuarantee base hb g hc W w (scale j) hW hw (hscale j) hj

/-- V2 is the genuine least attainable asymptotic coefficient over all
actual span-restricted M1 policies on the complete original physical
known-base source class. A different method may be selected at every
scale; the single explicit centred implementation attains the least value.
Use: completes the original two-dimensional known-base all-method minimax,
rather than only the hidden-disc scalar maximization or an operator game.
Article: main_krylov, thm:local(c), original exact asymptotic M1 minimax.
Proof: the genuine centred algorithm belongs to M1 and has the source-wide
V2 guarantee. Every other actual policy family obeys the proved physical
all-method asymptotic lower bound with the same original normalization. -/
theorem knownBaseTwoQuery_exact_asymptotic_minimax
    (base : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin 2)) (hc : referenceAtomCount base hb g=2)
    (W w : ℝ) (hW : 0< W) (hw : 0< w) (scale : ℕ → ℝ)
    (hscale : ∀ j,0< scale j) (hzero : Tendsto scale atTop (𝓝 0)) :
    IsLeast {v : ℝ | ∃ method : ℕ → OneGradientMethod (EuclideanSpace ℝ (Fin 2)),
      (∀ j,OneGradientSpanRestricted (method j)) ∧
        knownBaseTwoQueryAsymptoticGuarantee base g W w scale method v} (twoDimensionalValue W w) := by
  constructor
  · exact ⟨fun j => knownBaseCentredMethod base (W*scale j),
      fun j => knownBaseCentredMethod_spanRestricted base (W*scale j),
      knownBaseCentredMethod_asymptotic_guarantee base hb g hc W w hW hw.le scale hscale hzero⟩
  · rintro v ⟨method,hm,hbound⟩
    exact knownBaseTwoQuery_asymptotic_lower base hb g hc W w v hW hw scale hscale hzero method hm hbound

end
end krylov.OneGradient
