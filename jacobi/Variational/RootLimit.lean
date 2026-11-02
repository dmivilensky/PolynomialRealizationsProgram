import jacobi.Rearrangement.RadialReduction

/-!
Article: jacobi, Lemma D.1.
A root-mass-bounded sequence with convergent masses has an actual limiting
density at its finite lower limiting energy. Equimeasurable rearrangement
preserves the exact normalizations; root tightness preserves mass at the
constructed compactness limit. Every moment and Fredholm lower constraint
is retained in the extended lower-limit sense.
Source: equimeasurable rearrangement, Helly compactness, Fatou and root-mass tightness.
Use: the common analytic limit step in both branches of full Transfer and in lower semicontinuity of root infima.
-/
namespace jacobi.Variational
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- A root-normalized density sequence has an actual limiting competitor at its finite lower limiting cost.
Use: the common analytic limit step in both branches of full Transfer and in lower semicontinuity of root infima.
Article: jacobi, Lemma D.1.
Proof: select a subsequence whose costs tend to the lower limit, rearrange
it by the proved full theorem, and extract the proved radial compactness
subsequence. Root-mass tightness gives exact mass convergence. Fatou retains
the root bound and cost; spectral limits and Fredholm semicontinuity retain
every lower constraint simultaneously. -/
theorem root_limit_at_liminf (m : ℕ → Density) {M : ℝ}
    (hm : Tendsto (fun n => (m n).mass) atTop (𝓝 M))
    (hr : ∀ n, (m n).rootMass ≤ 1)
    (hL : liminf (fun n => (m n).cost) atTop ≠ ∞) :
    ∃ q : Density, SymmetricDecreasing q.value ∧ q.mass=M ∧ q.rootMass ≤ 1 ∧
      q.cost ≤ liminf (fun n => (m n).cost) atTop ∧
      (∀ i : Observation, liminf (fun n => ENNReal.ofReal (observe (m n) i)) atTop ≤
        ENNReal.ofReal (observe q i)) ∧
      ∀ s : ℝ, 0 ≤ s → liminf (fun n => (m n).fredholm s) atTop ≤ q.fredholm s := by
  -- Choose the cost lower-limit subsequence first, independently of every spectral observation.
  let L := liminf (fun n => (m n).cost) atTop
  obtain ⟨α,hcost,hα⟩ := exists_seq_tendsto_liminf (u := fun n => (m n).cost) (f := atTop)
  have heReal : Tendsto (fun n => (m (α n)).energy) atTop (𝓝 L.toReal) := by
    have ht := (ENNReal.tendsto_toReal hL).comp hcost
    simpa only [Function.comp_def,Density.cost_toReal] using ht
  obtain ⟨E,hE⟩ := heReal.bddAbove_range
  obtain ⟨B,hB⟩ := hm.bddAbove_range
  choose b hbs hbM hbE hbR hbDist hbO hbF hbP using
    fun n => jacobi.Rearrangement.exists_equimeasurable_rearrangement (m (α n))
  have hMb (n : ℕ) : (b n).mass ≤ B := by rw [hbM n]; exact hB (mem_range_self (α n))
  have hEb (n : ℕ) : (b n).energy ≤ E := by rw [hbE n]; exact hE (mem_range_self n)
  have hRb (n : ℕ) : (b n).rootMass ≤ ENNReal.ofReal (1 : ℝ) := by
    rw [hbR n,ENNReal.ofReal_one]
    exact hr (α n)
  obtain ⟨φ,hφ,q,hqs,hqM,hqE,hpoint,hqCost,hqRoot,hobs⟩ :=
    compact_subsequence b hbs hMb hEb
  have hpae : ∀ᵐ x, Tendsto (fun n => (b (φ n)).value x) atTop (𝓝 (q.value x)) := by
    have hz : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
    exact hz.mono hpoint
  -- The root constraint is kept before using it to establish tightness and exact mass.
  have hqR : q.rootMass ≤ 1 := hqRoot.trans (by
    have ht := liminf_le_liminf (f := atTop) (Eventually.of_forall fun n => hRb (φ n))
    simpa only [ENNReal.ofReal_one,liminf_const] using ht)
  have hL1 := global_l1_limit (b ∘ φ) q (fun n => hbs (φ n)) hqs
    (fun n => hEb (φ n)) hqE (by norm_num : (0 : ℝ) ≤ 1) (fun n => hRb (φ n)) hpae
  have hqMass : q.mass=M := by
    have h1 := mass_limit_of_l1 (b ∘ φ) q hL1
    have h2 := (hm.comp hα).comp hφ.tendsto_atTop
    have he (n : ℕ) : ((b ∘ φ) n).mass=(m (α (φ n))).mass := hbM (φ n)
    exact tendsto_nhds_unique h1 (h2.congr (fun n => (he n).symm))
  have hqC : q.cost ≤ L := by
    have he (n : ℕ) : (b n).cost=(m (α n)).cost := congrArg ENNReal.ofReal (hbE n)
    have ht := (hcost.congr (fun n => (he n).symm)).comp hφ.tendsto_atTop
    have hl := ht.liminf_eq
    simp only [Function.comp_def] at hl
    rwa [hl] at hqCost
  refine ⟨q,hqs,hqMass,hqR,hqC,fun i => ?_,fun s hs => ?_⟩
  · have hcomp := (hα.comp hφ.tendsto_atTop).liminf_le_liminf_comp
      (u := fun n => ENNReal.ofReal (observe (m n) i))
    have hmono := liminf_le_liminf (f := atTop) (Eventually.of_forall fun n =>
      ENNReal.ofReal_le_ofReal (hbO (φ n) i))
    have he := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hobs i)).liminf_eq
    simp only [Function.comp_def] at hcomp he
    exact hcomp.trans (hmono.trans_eq he)
  · have hcomp := (hα.comp hφ.tendsto_atTop).liminf_le_liminf_comp
      (u := fun n => (m n).fredholm s)
    have hmono := liminf_le_liminf (f := atTop) (Eventually.of_forall fun n => hbF (φ n) s hs)
    have hu := fredholm_limsup (b ∘ φ) q (fun n => hbs (φ n)) hqs
      (fun n => hMb (φ n)) hqM (fun n => hEb (φ n)) hqE hpae hs
    simp only [Function.comp_def] at hcomp
    exact hcomp.trans (hmono.trans (le_trans liminf_le_limsup hu))

end
end jacobi.Variational
