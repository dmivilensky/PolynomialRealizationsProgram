import polyak.Global.Sampling.PeriodicExtension
import polyak.Global.Sampling.AnalyticBranch

/-! Reflection of the real analytic half-circle branch. The first
 derivatives match even though the second derivatives can jump. -/
noncomputable section
namespace polyak.Global.Sampling
open Set Filter
open scoped Topology

def mirror (a : ℝ) (f : ℝ→ℝ) (x : ℝ) : ℝ :=
  if x≤a then f x else 2*a-f (2*a-x)

def mirrorDerivative (a : ℝ) (df : ℝ→ℝ) (x : ℝ) : ℝ :=
  if x≤a then df x else df (2*a-x)

theorem hasDerivAt_glue_le {f g : ℝ→ℝ} {a x d : ℝ}
    (hf : HasDerivAt f d x) (hg : HasDerivAt g d x)
    (he : x=a→f x=g x) : HasDerivAt (fun y=>if y≤a then f y else g y) d x := by
  rcases lt_trichotomy x a with hx|rfl|hx
  · apply hf.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    simp only [ite_eq_left hy.le]
  · have hl : HasDerivWithinAt (fun y=>if y≤x then f y else g y) d (Iic x) x := by
      apply hf.hasDerivWithinAt.congr_of_mem
      · intro y hy
        simp only [ite_eq_left (show y≤x from hy)]
      · exact Set.mem_Iic.mpr le_rfl
    have hr : HasDerivWithinAt (fun y=>if y≤x then f y else g y) d (Ioi x) x := by
      apply hg.hasDerivWithinAt.congr
      · intro y hy
        simp only [ite_eq_right (not_le.mpr (show x<y from hy))]
      · simp only [ite_eq_left le_rfl,he rfl]
    simpa only [Iic_union_Ioi,hasDerivWithinAt_univ] using hl.union hr
  · apply hg.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp only [ite_eq_right (not_le.mpr hy)]

theorem hasDerivAt_mirror {a : ℝ} (ha : 0<a) {f df : ℝ→ℝ}
    (hf : ∀x∈Icc 0 a,HasDerivAt f (df x) x) (he : f a=a)
    {x : ℝ} (hx : x∈Icc 0 (2*a)) :
    HasDerivAt (mirror a f) (mirrorDerivative a df x) x := by
  by_cases hxa : x≤a
  · by_cases heq : x=a
    · subst x
      have hfx:=hf a ⟨ha.le,le_rfl⟩
      have hmirror : HasDerivAt (fun y=>2*a-f (2*a-y)) (df a) a := by
        have hm : 2*a-a=a := by ring
        have hh := (hf a ⟨ha.le,le_rfl⟩).comp_of_eq a (h:=fun y=>2*a-y) ((hasDerivAt_id a).const_sub (2*a)) hm.symm
        simpa only [Function.comp_def,mul_neg_one,neg_neg] using hh.const_sub (2*a)
      rw [mirrorDerivative,ite_eq_left le_rfl]
      exact
        hasDerivAt_glue_le hfx hmirror (fun _=>by rw [show 2*a-a=a by ring,he]; ring)
    · have hlt : x<a := lt_of_le_of_ne hxa heq
      rw [mirrorDerivative,ite_eq_left hxa]
      apply (hf x ⟨hx.1,hxa⟩).congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds hlt] with y hy
      simp only [mirror,ite_eq_left hy.le]
  · have hlt : a<x := lt_of_not_ge hxa
    have hmem : 2*a-x∈Icc 0 a := by constructor <;> linarith [hx.2]
    have hh := (hf _ hmem).comp (h:=fun y=>2*a-y) x ((hasDerivAt_id x).const_sub (2*a))
    have hm : HasDerivAt (fun y=>2*a-f (2*a-y)) (df (2*a-x)) x := by
      simpa only [Function.comp_def,mul_neg_one,neg_neg] using hh.const_sub (2*a)
    rw [mirrorDerivative,ite_eq_right hxa]
    apply hm.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hlt] with y hy
    simp only [mirror,ite_eq_right (not_le.mpr hy)]


theorem continuousOn_mirrorDerivative {a : ℝ} {df : ℝ→ℝ}
    (hf : ∀x∈Icc 0 a,ContinuousAt df x) :
    ContinuousOn (mirrorDerivative a df) (Icc 0 (2*a)) := by
  unfold mirrorDerivative
  apply ContinuousOn.if
  · intro x hx
    have hx' : x∈frontier (Iic a) := hx.2
    rw [frontier_Iic,mem_singleton_iff] at hx'
    subst x
    congr 1
    ring
  · intro x hx
    have hx' : x∈closure (Iic a) := hx.2
    rw [isClosed_Iic.closure_eq] at hx'
    exact (hf x ⟨hx.1.1,hx'⟩).continuousWithinAt
  · intro x hx
    have he : {z:ℝ | ¬z≤a}=Ioi a := by ext z; simp only [mem_ofPred_eq,mem_Ioi,not_le]
    rw [he,closure_Ioi] at hx
    have hax : a≤x:=hx.2
    have hm : 2*a-x∈Icc 0 a := by constructor <;> linarith [hx.1.2]
    exact ((hf _ hm).comp (continuousAt_const.sub continuousAt_id)).continuousWithinAt

theorem hasDerivWithinAt_mirrorDerivative_right {a : ℝ} {df ddf : ℝ→ℝ}
    (hf : ∀x∈Icc 0 a,HasDerivAt df (ddf x) x)
    {x : ℝ} (hx : x∈Ico 0 (2*a)) :
    HasDerivWithinAt (mirrorDerivative a df)
      (if x<a then ddf x else -ddf (2*a-x)) (Ici x) x := by
  by_cases hxa : x<a
  · rw [ite_eq_left hxa]
    apply HasDerivAt.hasDerivWithinAt
    apply (hf x ⟨hx.1,hxa.le⟩).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hxa] with y hy
    simp only [mirrorDerivative,ite_eq_left hy.le]
  · rw [ite_eq_right hxa]
    have hax : a≤x := le_of_not_gt hxa
    have hm : 2*a-x∈Icc 0 a := by constructor <;> linarith [hx.2]
    have hh := (hf _ hm).comp (h:=fun y=>2*a-y) x ((hasDerivAt_id x).const_sub (2*a))
    have hd : HasDerivAt (fun y=>df (2*a-y)) (-ddf (2*a-x)) x := by
      simpa only [Function.comp_def,mul_neg_one] using hh
    apply hd.hasDerivWithinAt.congr_of_mem
    · intro y hy
      by_cases hya : y≤a
      · have hye : y=a := by linarith [show x≤y from hy]
        subst y
        simp only [mirrorDerivative,ite_eq_left le_rfl]
        congr 1
        ring
      · simp only [mirrorDerivative,ite_eq_right hya]
    · exact Set.mem_Ici.mpr le_rfl

end polyak.Global.Sampling
