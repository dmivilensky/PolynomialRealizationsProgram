import jacobi.Bessel.SturmComparison

/-!
Article: jacobi, Proposition B.1.
The strict Wronskian inequalities give actual comparator zeros on each
ordinary nodal interval and on the singular first interval. The comparator
sign is derived from continuity and absence of zeros, never assumed as a
property of an as yet unconstructed phase.
Use: derives the comparator sign needed by the genuine Sturm Wronskian argument.
-/
namespace jacobi.Bessel
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A continuous zero-free function has the same strict sign throughout an open interval as at any one of its points.
Use: derives the comparator sign needed by the genuine Sturm Wronskian argument.
Article: jacobi, Proposition B.1.
Proof: the intermediate value theorem on the connected interval would otherwise produce an actual zero. -/
theorem positive_on_interval_of_no_zero {f : ℝ → ℝ} {a b t : ℝ}
    (hf : ContinuousOn f (Ioo a b)) (hne : ∀ x∈Ioo a b,f x≠0)
    (ht : t∈Ioo a b) (hp : 0<f t) : ∀ x∈Ioo a b,0<f x := by
  intro x hx
  by_contra hn
  obtain ⟨z,hz,he⟩ := isPreconnected_Ioo.intermediate_value hx ht hf
    (show (0:ℝ)∈Icc (f x) (f t) from ⟨le_of_not_gt hn,hp.le⟩)
  exact hne z hz he

/-- A continuous function without an interior zero has one strict sign on every nonempty open interval.
Use: the actual nodal branch and comparator can be sign-normalized without a zero-orientation premise.
Article: jacobi, Proposition B.1.
Proof: choose the midpoint, where the function is nonzero, then propagate
its sign by the preceding connected-interval intermediate-value theorem. -/
theorem fixed_sign_on_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a<b)
    (hf : ContinuousOn f (Ioo a b)) (hne : ∀ x∈Ioo a b,f x≠0) :
    (∀ x∈Ioo a b,0<f x) ∨ (∀ x∈Ioo a b,f x<0) := by
  have hm : (a+b)/2∈Ioo a b := ⟨by linarith,by linarith⟩
  rcases lt_or_gt_of_ne (hne _ hm) with hn | hp
  · right
    have h := positive_on_interval_of_no_zero hf.neg
      (fun x hx => neg_ne_zero.mpr (hne x hx)) hm (neg_pos.mpr hn)
    exact fun x hx => neg_pos.mp (h x hx)
  · exact Or.inl (positive_on_interval_of_no_zero hf hne hm hp)

/-- A strictly more oscillatory actual solution has a genuine zero inside every positive ordinary nodal interval of the original solution.
Use: advances the canonical zero comparison by one full index.
Article: jacobi, Proposition B.1.
Proof: if the comparator had no zero, its actual continuous sign would
be fixed. Apply the proved strict Wronskian contradiction to that positive
sign or to the negative solution, which obeys the same genuine equation. -/
theorem sturm_zero_of_positive {f f' f'' g g' g'' q0 q1 : ℝ → ℝ} {a b : ℝ}
    (hab : a<b) (hf : ∀ x∈Icc a b,HasDerivAt f (f' x) x)
    (hf' : ∀ x∈Icc a b,HasDerivAt f' (f'' x) x)
    (hg : ∀ x∈Icc a b,HasDerivAt g (g' x) x)
    (hg' : ∀ x∈Icc a b,HasDerivAt g' (g'' x) x)
    (he0 : ∀ x∈Ioo a b,f'' x+q0 x*f x=0)
    (he1 : ∀ x∈Ioo a b,g'' x+q1 x*g x=0)
    (hq : ∀ x∈Ioo a b,q0 x<q1 x)
    (hfa : f a=0) (hfb : f b=0) (hp : ∀ x∈Ioo a b,0<f x) :
    ∃ x∈Ioo a b,g x=0 := by
  -- A sign choice is applied to the original comparator and its actual derivatives, not to an abstract surrogate.
  by_contra hn
  have hne : ∀ x∈Ioo a b,g x≠0 := by simpa only [not_exists,not_and] using hn
  have hc : ContinuousOn g (Ioo a b) := fun x hx =>
    (hg x ⟨hx.1.le,hx.2.le⟩).continuousAt.continuousWithinAt
  rcases fixed_sign_on_interval hab hc hne with hpos | hneg
  · exact not_positive_sturm_comparison hab hf hf' hg hg' he0 he1 hq hfa hfb hp hpos
  · apply not_positive_sturm_comparison (g := fun x => -g x) (g' := fun x => -g' x)
      (g'' := fun x => -g'' x) hab hf hf' (fun x hx => (hg x hx).neg)
      (fun x hx => (hg' x hx).neg) he0 (fun x hx => by linear_combination -he1 x hx)
      hq hfa hfb hp (fun x hx => neg_pos.mpr (hneg x hx))

/-- Strict Sturm comparison produces a genuine interior zero without assuming either sign of the original ordinary nodal branch.
Use: counts comparator zeros between every pair of consecutive actual Jacobi or Bessel zeros.
Article: jacobi, Proposition B.1.
Proof: continuity and the proved zero-free nodal interior fix the original
branch's sign. Apply the positive-branch result to that solution or its
negative; both have the actual same restoring coefficient and endpoint zeros. -/
theorem sturm_zero_between {f f' f'' g g' g'' q0 q1 : ℝ → ℝ} {a b : ℝ}
    (hab : a<b) (hf : ∀ x∈Icc a b,HasDerivAt f (f' x) x)
    (hf' : ∀ x∈Icc a b,HasDerivAt f' (f'' x) x)
    (hg : ∀ x∈Icc a b,HasDerivAt g (g' x) x)
    (hg' : ∀ x∈Icc a b,HasDerivAt g' (g'' x) x)
    (he0 : ∀ x∈Ioo a b,f'' x+q0 x*f x=0)
    (he1 : ∀ x∈Ioo a b,g'' x+q1 x*g x=0)
    (hq : ∀ x∈Ioo a b,q0 x<q1 x)
    (hfa : f a=0) (hfb : f b=0) (hne : ∀ x∈Ioo a b,f x≠0) :
    ∃ x∈Ioo a b,g x=0 := by
  -- Only the genuinely zero-free interval between the original consecutive zeros is used.
  have hc : ContinuousOn f (Ioo a b) := fun x hx =>
    (hf x ⟨hx.1.le,hx.2.le⟩).continuousAt.continuousWithinAt
  rcases fixed_sign_on_interval hab hc hne with hp | hn
  · exact sturm_zero_of_positive hab hf hf' hg hg' he0 he1 hq hfa hfb hp
  · apply sturm_zero_of_positive (f := fun x => -f x) (f' := fun x => -f' x)
      (f'' := fun x => -f'' x) hab (fun x hx => (hf x hx).neg)
      (fun x hx => (hf' x hx).neg) hg hg'
      (fun x hx => by linear_combination -he0 x hx) he1 hq
      (by simpa only [neg_eq_zero] using hfa) (by simpa only [neg_eq_zero] using hfb)
      (fun x hx => neg_pos.mpr (hn x hx))

/-- Singular Sturm comparison produces an actual zero on the first nodal interval of the original selected positive branch.
Use: starts the correctly numbered comparison of the actual Jacobi and Bessel zero lists, including the singular endpoint range.
Article: jacobi, Proposition B.1.
Proof: without a comparator zero its genuine initial positive sign
propagates by connectedness. The proved singular Wronskian theorem then
contradicts strict coefficient ordering and the actual zero boundary limit. -/
theorem singular_sturm_zero {f f' f'' g g' g'' q0 q1 : ℝ → ℝ} {b : ℝ}
    (hb : 0<b) (hf : ∀ x∈Ioc 0 b,HasDerivAt f (f' x) x)
    (hf' : ∀ x∈Ioc 0 b,HasDerivAt f' (f'' x) x)
    (hg : ∀ x∈Ioc 0 b,HasDerivAt g (g' x) x)
    (hg' : ∀ x∈Ioc 0 b,HasDerivAt g' (g'' x) x)
    (he0 : ∀ x∈Ioo 0 b,f'' x+q0 x*f x=0)
    (he1 : ∀ x∈Ioo 0 b,g'' x+q1 x*g x=0)
    (hq : ∀ x∈Ioo 0 b,q0 x<q1 x)
    (hlim : Tendsto (fun x => f' x*g x-f x*g' x) (𝓝[>] 0) (𝓝 0))
    (hfb : f b=0) (hp : ∀ x∈Ioo 0 b,0<f x)
    (hinit : ∀ᶠ x in 𝓝[>] (0:ℝ),0<g x) : ∃ x∈Ioo 0 b,g x=0 := by
  -- The comparator's positive branch comes from its actual selected endpoint factor, not an assumed phase normalization.
  by_contra hn
  have hne : ∀ x∈Ioo 0 b,g x≠0 := by simpa only [not_exists,not_and] using hn
  have hpoint : ∀ᶠ x in 𝓝[>] (0:ℝ),x∈Ioo 0 b ∧ 0<g x :=
    Filter.Eventually.and (Ioo_mem_nhdsGT hb) hinit
  obtain ⟨t,ht,hpt⟩ := hpoint.exists
  have hc : ContinuousOn g (Ioo 0 b) := fun x hx =>
    (hg x ⟨hx.1,hx.2.le⟩).continuousAt.continuousWithinAt
  exact not_positive_singular_sturm hb hf hf' hg hg' he0 he1 hq hlim hfb hp
    (positive_on_interval_of_no_zero hc hne ht hpt)

end
end jacobi.Bessel
