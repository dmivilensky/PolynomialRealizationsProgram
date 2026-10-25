import polyak.Levels.Chart.Coefficients
import Mathlib.Topology.Order.IntermediateValue

/-! A real algebraic construction of the stable factor. Its scalar secular
equation has one root on the stable branch; no root-selection hypothesis or
quartic argument principle is assumed. -/
noncomputable section
namespace polyak.Levels.Chart
open Set

def secular (a v t d : ℝ) : ℝ := d+v^2/d-2*t-1/(d-2*a)

theorem secular_difference {a v t d e : ℝ} (hd : d≠0) (he : e≠0)
    (hda : d-2*a≠0) (hea : e-2*a≠0) :
    secular a v t e-secular a v t d=
      (e-d)*(1-v^2/(d*e))+(e-d)/((d-2*a)*(e-2*a)) := by
  unfold secular
  field_simp
  ring

theorem secular_strictMono {a v t d e : ℝ} (ha : 0<a) (hda : 2*a<d)
    (hdv : |v|≤d) (hde : d<e) : secular a v t d<secular a v t e := by
  have hd0 : 0<d := by linarith
  have he0 : 0<e := hd0.trans hde
  have hea : 2*a<e := hda.trans hde
  apply sub_pos.mp
  rw [secular_difference hd0.ne' he0.ne' (sub_pos.mpr hda).ne' (sub_pos.mpr hea).ne']
  have hvd : v^2≤d^2 := by nlinarith [sq_abs v,abs_nonneg v]
  have hve : v^2≤d*e := by nlinarith [mul_pos hd0 (sub_pos.mpr hde)]
  have hf : 0≤1-v^2/(d*e) := by
    apply sub_nonneg.mpr
    exact (div_le_one (mul_pos hd0 he0)).mpr hve
  exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_pos.mpr hde).le hf)
    (div_pos (sub_pos.mpr hde) (mul_pos (sub_pos.mpr hda) (sub_pos.mpr hea)))

theorem secular_exists_unique {a v t : ℝ} (ha : 0<a) (ht : |v|<t) :
    ∃! d : ℝ,2*a<d ∧ |v|<d ∧ secular a v t d=0 := by
  have ht0 : 0<t := (abs_nonneg v).trans_lt ht
  let D := 4*a+2*t+4
  have hD : 0<D := by dsimp [D]; positivity
  let δ := min 1 (min ((t-|v|)/2) (1/D))
  have hδ : 0<δ := lt_min zero_lt_one
    (lt_min (by linarith) (one_div_pos.mpr hD))
  have hδ1 : δ≤1 := min_le_left _ _
  have hδt : δ≤(t-|v|)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδD : δ≤1/D := (min_le_right _ _).trans (min_le_right _ _)
  have hDδ : D≤1/δ := by
    apply (le_div_iff₀ hδ).mpr
    have hh := (le_div_iff₀ hD).mp hδD
    nlinarith
  let l := max (2*a) |v|+δ
  have hla : 2*a<l := by have := le_max_left (2*a) |v|; dsimp [l]; linarith
  have hlv : |v|<l := by have := le_max_right (2*a) |v|; dsimp [l]; linarith
  have hl0 : 0<l := by linarith
  have hvbound : v^2/l≤l := by
    apply (div_le_iff₀ hl0).mpr
    nlinarith [sq_abs v,abs_nonneg v]
  have hgl : secular a v t l<0 := by
    rcases le_total (2*a) |v| with h|h
    · have he : l=|v|+δ := by dsimp [l]; rw [max_eq_right h]
      have hinv : 0<1/(l-2*a) := one_div_pos.mpr (sub_pos.mpr hla)
      rw [he] at hinv
      unfold secular
      rw [he] at hvbound ⊢
      nlinarith
    · have he : l=2*a+δ := by dsimp [l]; rw [max_eq_left h]
      have he' : l-2*a=δ := by linarith
      unfold secular
      rw [he']
      dsimp [D] at hDδ
      nlinarith
  let r := l+2*t+2*a+4
  have hlr : l<r := by dsimp [r]; linarith
  have hra : 2*a<r := hla.trans hlr
  have hr0 : 0<r := hl0.trans hlr
  have hgr : 0<secular a v t r := by
    have hden : 1<r-2*a := by dsimp [r]; linarith
    have hinv : 1/(r-2*a)<1 := (div_lt_one (by linarith)).mpr hden
    have hv : 0≤v^2/r := div_nonneg (sq_nonneg _) hr0.le
    unfold secular
    dsimp [r] at *
    linarith
  have hcont : ContinuousOn (secular a v t) (Icc l r) := by
    unfold secular
    fun_prop (disch := intro d hd; apply ne_of_gt; linarith [hd.1])
  have hz : (0:ℝ)∈Icc (secular a v t l) (secular a v t r) := ⟨hgl.le,hgr.le⟩
  obtain ⟨d,hd,hzero⟩ := intermediate_value_Icc hlr.le hcont hz
  have hdl : l<d := by
    apply lt_of_le_of_ne hd.1
    intro he
    rw [he,hzero] at hgl
    exact lt_irrefl _ hgl
  refine ⟨d,⟨hla.trans hdl,hlv.trans hdl,hzero⟩,?_⟩
  intro e he
  rcases lt_trichotomy e d with h|h|h
  · have hh := secular_strictMono (t:=t) ha he.1 he.2.1.le h
    rw [he.2.2,hzero] at hh
    exact False.elim (lt_irrefl _ hh)
  · exact h
  · have hh := secular_strictMono (t:=t) ha (hla.trans hdl) (hlv.trans hdl).le h
    rw [he.2.2,hzero] at hh
    exact False.elim (lt_irrefl _ hh)

end polyak.Levels.Chart
