import krylov.ContinuumBV.ChainPartitions
import krylov.ContinuumBV.UniformTaylor
import krylov.ContinuumBV.EqualGrid

/-!
Article: main_krylov, apC:lem:fund, continuous nonlinear BV chain rule.
Use: prove the full continuous-path chain identity from C¹ regularity on a
compact state domain. The proof constructs genuine equal time grids;
neither a derivative-oscillation modulus nor an integral identity is assumed.
Singular continuous variation is included in the Stieltjes vector integral.
Source: uniform Taylor control, Heine–Cantor, and the two proved sum limits.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Genuine continuous nonlinear BV chain rule. The state may vary with a
singular continuous measure; it need not be absolutely continuous in time. -/
theorem continuous_chain_contDiff_compact {z : ℝ → E}
    (hz : BoundedVariationOn z univ) (hzc : Continuous z) {F : E → ℝ} {s : Set E}
    (hc : IsCompact s) (hmap : MapsTo z univ s)
    (hF : ∀ w ∈ s, ContDiffAt ℝ 1 F w) {a b : ℝ} (hab : a ≤ b) :
    (∫ᵛ x in Ioc a b, fderiv ℝ F (z x) ∂[derivativePairing; hz.vectorMeasure]) =
      F (z b) - F (z a) := by
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos : ∀ k, 0 < ε k := by intro k; dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose η hη hosc using fun k => exists_uniform_local_taylor_data hc hF (hεpos k)
  have hzu : UniformContinuousOn z (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hzc.continuousOn
  choose δ hδ htime using fun k => Metric.uniformContinuousOn_iff.1 hzu (η k) (hη k)
  choose N hN ht ha hb hmem hmesh using fun k => exists_equalGrid hab (hδ k)
  let t : ℕ → ℕ → ℝ := fun k => equalGrid a b (N k)
  have hclose : ∀ k i, i < N k →
      ‖z (t k (i + 1)) - z (t k i)‖ < η k := by
    intro k i hi
    have hd : dist (t k (i + 1)) (t k i) < δ k := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (ht k (Nat.le_succ i)))]
      exact hmesh k i hi
    simpa only [dist_eq_norm] using
      htime k (t k (i + 1)) (hmem k (i + 1)) (t k i) (hmem k i) hd
  have hcoef : Continuous (fun x => fderiv ℝ F (z x)) := by
    apply continuous_iff_continuousAt.2
    intro x
    exact ((hF (z x) (hmap (mem_univ x))).continuousAt_fderiv (by norm_num)).comp hzc.continuousAt
  have hint : (hz.vectorMeasure.restrict (Ioc a b)).Integrable
      (fun x => fderiv ℝ F (z x)) := by
    change Integrable (fun x => fderiv ℝ F (z x))
      (hz.vectorMeasure.restrict (Ioc a b)).variation
    rw [VectorMeasure.variation_restrict measurableSet_Ioc]
    exact hcoef.integrableOn_Ioc
  apply continuous_chain_of_partitions hz hzc t N ε ht ha hb
  · intro k i hi w hw
    exact (hosc k (z (t k i)) (hmap (mem_univ _))
      (z (t k (i + 1))) (hclose k i hi) w hw).1
  · intro k i hi w hw
    exact (hosc k (z (t k i)) (hmap (mem_univ _))
      (z (t k (i + 1))) (hclose k i hi) w hw).2
  · intro k i hi x hx
    have hxmem : x ∈ Icc a b :=
      ⟨(hmem k i).1.trans hx.1.le, hx.2.trans (hmem k (i + 1)).2⟩
    have hdist : dist x (t k i) < δ k := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hx.1.le)]
      exact (sub_le_sub_right hx.2 _).trans_lt (hmesh k i hi)
    have hstate : ‖z x - z (t k i)‖ < η k := by
      simpa only [dist_eq_norm] using htime k x hxmem (t k i) (hmem k i) hdist
    rw [norm_sub_rev]
    exact (hosc k (z (t k i)) (hmap (mem_univ _)) (z x)
      hstate (z x) (right_mem_segment ℝ _ _)).2
  · exact fun k => (hεpos k).le
  · exact hεlim
  · exact hint

end
end krylov.ContinuumBV
