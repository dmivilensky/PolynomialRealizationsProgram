import polyak.Global.Symbols.Compactness

/-! Weak convergence against c₀ test sequences retains exactly the mass
which escapes every finite set in the minimizer coefficient. -/
noncomputable section
namespace polyak.Global.Symbols
open Levels Filter Topology
open scoped BigOperators

theorem Weights.weighted_summable {𝒩 : Set ℤ} (a : Weights 𝒩) {f : ℤ→ℝ} {M : ℝ}
    (hb : ∀n,‖f n‖≤M) : Summable (fun n=>a.weight n*f n) := by
  apply (a.summable.mul_left M).of_norm_bounded
  intro n
  rw [norm_mul,Real.norm_of_nonneg (a.nonneg n)]
  have hh := mul_le_mul_of_nonneg_left (hb n) (a.nonneg n)
  nlinarith

theorem Weights.weighted_tail_bound {𝒩 : Set ℤ} (a : Weights 𝒩) (f : ℤ→ℝ)
    {ε : ℝ} (hε : 0≤ε) (F : Finset ℤ) (hb : ∀n,n∉F→‖f n‖≤ε) :
    ‖∑'n : {n : ℤ // n∉F},a.weight n*f n‖≤ε := by
  have hs : Summable (fun n : {n : ℤ // n∉F}=>ε*a.weight n) :=
    (a.summable.subtype _).mul_left ε
  have hn (n : {n : ℤ // n∉F}) : ‖a.weight n*f n‖≤ε*a.weight n := by
    rw [norm_mul,Real.norm_of_nonneg (a.nonneg n)]
    have hh := mul_le_mul_of_nonneg_left (hb n n.property) (a.nonneg n)
    nlinarith
  have hsn : Summable (fun n : {n : ℤ // n∉F}=>‖a.weight n*f n‖) :=
    hs.of_nonneg_of_le (fun _=>norm_nonneg _) hn
  have ht : (∑'n : {n : ℤ // n∉F},a.weight n)≤1 := by
    have he := a.summable.sum_add_tsum_subtype_compl F
    have hp := Finset.sum_nonneg (fun n (_ : n∈F)=>a.nonneg n)
    linarith [a.mass_le_one]
  calc
    _≤∑'n : {n : ℤ // n∉F},‖a.weight n*f n‖ := norm_tsum_le_tsum_norm hsn
    _≤∑'n : {n : ℤ // n∉F},ε*a.weight n := hsn.tsum_le_tsum hn hs
    _=ε*(∑'n : {n : ℤ // n∉F},a.weight n) := tsum_mul_left
    _≤ε := by nlinarith

theorem weighted_tsum_tendsto {𝒩 : Set ℤ} (a : ℕ→Weights 𝒩) (b : Weights 𝒩)
    (hc : ∀n,Tendsto (fun j=>(a j).weight n) atTop (𝓝 (b.weight n)))
    (f : ℕ→ℤ→ℝ) (g : ℤ→ℝ) {M : ℝ}
    (hb : ∀j n,‖f j n‖≤M) (hgb : ∀n,‖g n‖≤M)
    (hf : ∀n,Tendsto (fun j=>f j n) atTop (𝓝 (g n)))
    (htail : ∀ε : ℝ,0<ε→∃F : Finset ℤ,
      (∀j n,n∉F→‖f j n‖≤ε) ∧ (∀n,n∉F→‖g n‖≤ε)) :
    Tendsto (fun j=>∑'n,(a j).weight n*f j n) atTop
      (𝓝 (∑'n,b.weight n*g n)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨F,hF,hG⟩ := htail (ε/3) (by linarith)
  have hhead : Tendsto (fun j=>∑n∈F,(a j).weight n*f j n) atTop
      (𝓝 (∑n∈F,b.weight n*g n)) :=
    tendsto_finsetSum F (fun n _=>(hc n).mul (hf n))
  filter_upwards [(Metric.tendsto_nhds.mp hhead) (ε/3) (by linarith)] with j hj
  have ha := (a j).weighted_summable (hb j)
  have hg := b.weighted_summable hgb
  have ht₁ := (a j).weighted_tail_bound (f j) (by linarith : 0≤ε/3) F (hF j)
  have ht₂ := b.weighted_tail_bound g (by linarith : 0≤ε/3) F hG
  rw [dist_eq_norm,←ha.sum_add_tsum_subtype_compl F,←hg.sum_add_tsum_subtype_compl F]
  have he : (∑n∈F,(a j).weight n*f j n)+
        (∑'n : {n : ℤ // n∉F},(a j).weight n*f j n)-
      ((∑n∈F,b.weight n*g n)+(∑'n : {n : ℤ // n∉F},b.weight n*g n))=
      ((∑n∈F,(a j).weight n*f j n)-(∑n∈F,b.weight n*g n))+
        ((∑'n : {n : ℤ // n∉F},(a j).weight n*f j n)-
          (∑'n : {n : ℤ // n∉F},b.weight n*g n)) := by ring
  rw [he]
  have hn := norm_add_le
    ((∑n∈F,(a j).weight n*f j n)-(∑n∈F,b.weight n*g n))
    ((∑'n : {n : ℤ // n∉F},(a j).weight n*f j n)-
      (∑'n : {n : ℤ // n∉F},b.weight n*g n))
  have hd := norm_sub_le
    (∑'n : {n : ℤ // n∉F},(a j).weight n*f j n)
    (∑'n : {n : ℤ // n∉F},b.weight n*g n)
  rw [dist_eq_norm] at hj
  linarith

end polyak.Global.Symbols
