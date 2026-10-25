import polyak.FareyPlateau.FanAnalysis.OriginJets
import polyak.FareyPlateau.FanAnalysis.NecessityCore
import Mathlib.Analysis.Normed.Ring.Lemmas

/-! The origin constraints force the normalized near mass to converge to
(k-1)/k. This conclusion applies to arbitrary feasible masses, not only the
explicit constructive family. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Filter
open scoped Topology

private theorem bounded_mass {X : Type*} {l : Filter X} {w v : X → ℝ}
    (hw : ∀ᶠ x in l, 0 ≤ w x ∧ 0 ≤ v x ∧ w x+v x=1) :
    IsBoundedUnder (· ≤ ·) l (norm ∘ w) := by
  refine ⟨1, ?_⟩
  change ∀ᶠ x in l, ‖w x‖ ≤ 1
  filter_upwards [hw] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  linarith [hx.2.1, hx.2.2]

theorem normalized_mass_limit {X : Type*} {l : Filter X} {δ wa wc : X → ℝ}
    {P₁ P₂ M₁ M₂ : ℝ → ℝ} {m t : ℝ} (hm : 0 < m) (ht : 0 < t)
    (hδ : Tendsto δ l (𝓝[≠] 0))
    (hP₁ : Tendsto (fun z => P₁ z/z) (𝓝[≠] 0) (𝓝 (-t)))
    (hP₂ : Tendsto (fun z => P₂ z/z) (𝓝[≠] 0) (𝓝 (m*t)))
    (hM₁ : Tendsto (fun z => M₁ z/z) (𝓝[≠] 0) (𝓝 t))
    (hM₂ : Tendsto (fun z => M₂ z/z) (𝓝[≠] 0) (𝓝 (-m*t)))
    (hw : ∀ᶠ x in l, 0 ≤ wa x ∧ 0 ≤ wc x ∧ wa x+wc x=1)
    (hfeas : ∀ᶠ x in l, 0 ≤ wa x*P₁ (δ x)+wc x*P₂ (δ x) ∧
      0 ≤ wa x*M₁ (δ x)+wc x*M₂ (δ x)) :
    Tendsto wa l (𝓝 (m/(m+1))) := by
  let p := fun x => wa x*(P₁ (δ x)/δ x)+wc x*(P₂ (δ x)/δ x)
  let r := fun x => wa x*(M₁ (δ x)/δ x)+wc x*(M₂ (δ x)/δ x)
  have hwa := bounded_mass hw
  have hwc := bounded_mass (hw.mono fun x hx => ⟨hx.2.1,hx.1,by linarith [hx.2.2]⟩)
  have hsum₁ : Tendsto (fun x => P₁ (δ x)/δ x+M₁ (δ x)/δ x) l (𝓝 0) := by
    simpa only [Function.comp_def, neg_add_cancel] using (hP₁.comp hδ).add (hM₁.comp hδ)
  have hsum₂ : Tendsto (fun x => P₂ (δ x)/δ x+M₂ (δ x)/δ x) l (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul, add_neg_cancel] using (hP₂.comp hδ).add (hM₂.comp hδ)
  have hsum : Tendsto (fun x => p x+r x) l (𝓝 0) := by
    have hh := (isBoundedUnder_le_mul_tendsto_zero hwa hsum₁).add
      (isBoundedUnder_le_mul_tendsto_zero hwc hsum₂)
    convert hh using 1
    · ext x
      dsimp [p,r]
      ring
    · simp only [add_zero]
  have habs : ∀ᶠ x in l, |p x| ≤ |p x+r x| := by
    filter_upwards [hfeas,hδ.eventually self_mem_nhdsWithin] with x hx hz
    have hzn : δ x ≠ 0 := hz
    have hp : δ x*p x=wa x*P₁ (δ x)+wc x*P₂ (δ x) := by dsimp [p]; field_simp
    have hr : δ x*r x=wa x*M₁ (δ x)+wc x*M₂ (δ x) := by dsimp [r]; field_simp
    rcases lt_or_gt_of_ne hzn with hn | hn
    · have hpneg : p x ≤ 0 := by nlinarith [hx.1]
      have hrneg : r x ≤ 0 := by nlinarith [hx.2]
      rw [abs_of_nonpos hpneg,abs_of_nonpos (by linarith)]
      linarith
    · have hppos : 0 ≤ p x := by nlinarith [hx.1]
      have hrpos : 0 ≤ r x := by nlinarith [hx.2]
      rw [abs_of_nonneg hppos,abs_of_nonneg (by linarith)]
      linarith
  have hp : Tendsto p l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using
      (squeeze_zero' (Eventually.of_forall fun x => abs_nonneg (p x)) habs (by simpa only [abs_zero] using hsum.abs))
  have hn : -t-m*t ≠ 0 := by nlinarith
  have hquot := (hp.sub (hP₂.comp hδ)).div ((hP₁.comp hδ).sub (hP₂.comp hδ)) hn
  have hden : ∀ᶠ x in l, P₁ (δ x)/δ x-P₂ (δ x)/δ x ≠ 0 :=
    ((hP₁.comp hδ).sub (hP₂.comp hδ)).eventually_ne hn
  have he : wa =ᶠ[l] fun x => (p x-P₂ (δ x)/δ x)/(P₁ (δ x)/δ x-P₂ (δ x)/δ x) := by
    filter_upwards [hw,hden] with x hx hdx
    apply (eq_div_iff hdx).mpr
    dsimp [p]
    linear_combination -(P₂ (δ x)/δ x)*hx.2.2
  have hvalue : (0-m*t)/(-t-m*t)=m/(m+1) := by
    have hmz : m+1≠0 := by linarith
    have htz : t≠0 := ht.ne'
    rw [show -t-m*t = -(t*(m+1)) by ring]
    field_simp
    ring
  rw [hvalue] at hquot
  exact hquot.congr' he.symm

namespace Actual
open General Levels ModeLocking
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem fan_mass_fraction {X : Type*} {l : Filter X} {δ wa wc : X → ℝ} (e : ℝ)
    (hδ : Tendsto δ l (𝓝[≠] 0))
    (hw : ∀ᶠ x in l, 0 ≤ wa x ∧ 0 ≤ wc x ∧ wa x+wc x=1)
    (hfeas : ∀ᶠ x in l, ∃P : Fan.Data, P.k=k ∧ P.delta=δ x ∧
      ∀n : ℤ, 0 ≤ pairLag A P e (δ x) (wa x) (wc x) n) :
    Tendsto wa l (𝓝 (((k : ℝ)-1)/k)) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast A.period_ge
  have hs := sin_positive A
  have hm : 0<(k : ℝ)-1 := by linarith
  have ht : 0<(k : ℝ)*Real.sin (Real.pi/k) := by positivity
  have hp₁ := near_origin_limit A e (k : ℝ)
  have hp₂ := far_origin_limit A e (-((k : ℝ)-1)*k)
  have hm₁ := near_origin_limit A e (-(k : ℝ))
  have hm₂ := far_origin_limit A e (((k : ℝ)-1)*k)
  have hh := normalized_mass_limit hm ht hδ
    (by convert hp₁ using 1; congr 1; ring)
    (by convert hp₂ using 1; congr 1; ring)
    (by convert hm₁ using 1; congr 1; ring)
    (by convert hm₂ using 1; congr 1; ring) hw (show ∀ᶠ x in l, _ from ?_)
  · simpa only [sub_add_cancel] using hh
  · filter_upwards [hfeas] with x hx
    obtain ⟨P,hk,hPd,hF⟩ := hx
    exact ⟨by simpa only [Int.cast_one,one_mul] using origin_constraint A P hk hPd hF 1,
      by simpa only [Int.cast_neg,Int.cast_one,neg_one_mul,mul_neg,neg_neg,neg_mul,one_mul]
        using origin_constraint A P hk hPd hF (-1)⟩

end Actual
end polyak.FareyPlateau.FanAnalysis
