import polyak.Global.Symbols.Series
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Countable diagonal compactness of all signed-lag coefficients. Finite
partial sums pass to the limit and prove the full mass bound (Fatou). -/
noncomputable section
namespace polyak.Global.Symbols
open Levels Set Filter Topology
open scoped BigOperators

theorem Weights.weight_le_one {𝒩 : Set ℤ} (a : Weights 𝒩) (n : ℤ) : a.weight n≤1 :=
  (a.summable.le_tsum n (fun k _=>a.nonneg k)).trans a.mass_le_one

theorem Weights.sum_le_one {𝒩 : Set ℤ} (a : Weights 𝒩) (F : Finset ℤ) :
    ∑n∈F,a.weight n≤1 :=
  (a.summable.sum_le_tsum F (fun n _=>a.nonneg n)).trans a.mass_le_one

theorem exists_coefficient_subsequence {𝒩 : Set ℤ} (a : ℕ→Weights 𝒩) :
    ∃b : Weights 𝒩,∃φ : ℕ→ℕ,StrictMono φ ∧
      ∀n : ℤ,Tendsto (fun j=>(a (φ j)).weight n) atTop (𝓝 (b.weight n)) := by
  let cube : ℕ→ℤ→Icc (0:ℝ) 1 :=
    fun j n=>⟨(a j).weight n,(a j).nonneg n,(a j).weight_le_one n⟩
  obtain ⟨c,φ,hφ,hc⟩ := CompactSpace.tendsto_subseq cube
  have hn (n : ℤ) : Tendsto (fun j=>(a (φ j)).weight n) atTop (𝓝 (c n:ℝ)) := by
    exact (continuous_subtype_val.continuousAt.tendsto).comp
      ((tendsto_pi_nhds.mp hc) n)
  have hfinite (F : Finset ℤ) : ∑n∈F,(c n:ℝ)≤1 := by
    apply le_of_tendsto (tendsto_finsetSum F (fun n _=>hn n))
    exact Eventually.of_forall (fun j=>(a (φ j)).sum_le_one F)
  have hnon : ∀n,0≤(c n:ℝ) := fun n=>(c n).property.1
  have hout (n : ℤ) (hnN : n∉𝒩) : (c n:ℝ)=0 := by
    apply tendsto_nhds_unique (hn n)
    have he : (fun j=>(a (φ j)).weight n)=fun _=>0 := funext (fun j=>(a (φ j)).outside n hnN)
    rw [he]
    exact tendsto_const_nhds
  let b : Weights 𝒩 := {
    weight := fun n=>(c n:ℝ)
    nonneg := hnon
    outside := hout
    summable := summable_of_sum_le hnon hfinite
    mass_le_one := Real.tsum_le_of_sum_le hnon hfinite }
  exact ⟨b,φ,hφ,hn⟩

end polyak.Global.Symbols
