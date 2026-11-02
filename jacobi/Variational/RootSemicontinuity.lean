import jacobi.Variational.RootLimit
import jacobi.Variational.InfimumSequence

/-!
Article: jacobi, Appendix D.1.
The actual joint moment and Fredholm infima are lower semicontinuous under
convergence of masses and thresholds. Near-minimizing densities are selected
from the actual admissible sets; finite lower limiting cost supplies their
existence. The proved equimeasurable root-compactness limit retains exact
mass, root normalization and every active spectral constraint.
Source: sequential infimum approximation and the direct root-mass compactness argument.
Use: passes the uniform packed-fibre lower bound to its limiting edge thresholds in full Transfer.
-/
namespace jacobi.Variational
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The actual joint moment root infimum is lower semicontinuous in its mass and active thresholds.
Use: passes the uniform packed-fibre lower bound to its limiting edge thresholds in full Transfer.
Article: jacobi, Appendix D.1 (lower semicontinuity).
Proof: if the lower limit is finite, select actual near-minimizers converging
to that cost. The proved root limit preserves exact mass and the root bound;
threshold convergence and moment lower limits retain admissibility. Its cost
then bounds the limiting actual infimum. -/
theorem rootInfimum_liminf (S : Set Observation) (Mseq : ℕ → ℝ) (Tseq : ℕ → Observation → ℝ)
    {M : ℝ} {T : Observation → ℝ} (hM : Tendsto Mseq atTop (𝓝 M))
    (hT : ∀ i ∈ S, Tendsto (fun n => Tseq n i) atTop (𝓝 (T i))) :
    rootInfimum S M T ≤ liminf (fun n => rootInfimum S (Mseq n) (Tseq n)) atTop := by
  -- Infinite lower limiting cost is automatic; finite cost supplies actual admissible witnesses.
  by_cases hL : liminf (fun n => rootInfimum S (Mseq n) (Tseq n)) atTop=∞
  · rw [hL]; exact le_top
  let A (n : ℕ) : Set Density := {m | m.mass=Mseq n ∧ m.rootMass ≤ 1 ∧ ∀ i ∈ S, Tseq n i ≤ observe m i}
  obtain ⟨α,hα,m,hm,hcost⟩ := exists_liminf_competitors (X := fun _ => Density)
    (fun _ => Density.cost) A hL
  have hmass : Tendsto (fun n => (m n).mass) atTop (𝓝 M) :=
    (hM.comp hα).congr (fun n => (hm n).1.symm)
  have he := hcost.liminf_eq
  have hfin : liminf (fun n => (m n).cost) atTop ≠ ∞ := by rwa [he]
  obtain ⟨q,hqs,hqM,hqR,hqC,hqO,hqF⟩ := root_limit_at_liminf m hmass (fun n => (hm n).2.1) hfin
  have hqT (i : Observation) (hi : i ∈ S) : T i ≤ observe q i := by
    have ht := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hT i hi).comp hα)).liminf_eq
    have hb := liminf_le_liminf (f := atTop) (Eventually.of_forall fun n =>
      ENNReal.ofReal_le_ofReal ((hm n).2.2 i hi))
    simp only [Function.comp_def] at ht
    rw [ht] at hb
    have hn : 0 ≤ observe q i := by
      cases i with
      | second => exact tsum_nonneg (fun j => sq_nonneg _)
      | top => exact (chebyshev2.Continuum.kernelSpectralData q.integrable q.nonneg).eigenvalue_nonneg 0
    exact (ENNReal.ofReal_le_ofReal_iff hn).mp (hb.trans (hqO i))
  apply (sInf_le ⟨q,⟨hqM,hqR,hqT⟩,rfl⟩ : rootInfimum S M T ≤ q.cost).trans
  rwa [he] at hqC

/-- The actual root-normalized Fredholm infimum is lower semicontinuous in its mass and extended threshold.
Use: the Fredholm branch of full Transfer, including possible limiting pole values.
Article: jacobi, Appendix D.1 (lower semicontinuity).
Proof: actual near-minimizers converge to the finite lower limiting cost.
The constructed root limit keeps exact mass and normalization; its extended
Fredholm lower-limit comparison and threshold convergence retain admissibility. -/
theorem rootFredholmInfimum_liminf {s : ℝ} (hs : 0 ≤ s) (Mseq : ℕ → ℝ) (dseq : ℕ → ℝ≥0∞)
    {M : ℝ} {d : ℝ≥0∞} (hM : Tendsto Mseq atTop (𝓝 M)) (hd : Tendsto dseq atTop (𝓝 d)) :
    rootFredholmInfimum s M d ≤ liminf (fun n => rootFredholmInfimum s (Mseq n) (dseq n)) atTop := by
  -- The limiting determinant target is allowed to be infinite throughout this argument.
  by_cases hL : liminf (fun n => rootFredholmInfimum s (Mseq n) (dseq n)) atTop=∞
  · rw [hL]; exact le_top
  let A (n : ℕ) : Set Density := {m | m.mass=Mseq n ∧ m.rootMass ≤ 1 ∧ dseq n ≤ m.fredholm s}
  obtain ⟨α,hα,m,hm,hcost⟩ := exists_liminf_competitors (X := fun _ => Density)
    (fun _ => Density.cost) A hL
  have hmass : Tendsto (fun n => (m n).mass) atTop (𝓝 M) :=
    (hM.comp hα).congr (fun n => (hm n).1.symm)
  have he := hcost.liminf_eq
  have hfin : liminf (fun n => (m n).cost) atTop ≠ ∞ := by rwa [he]
  obtain ⟨q,hqs,hqM,hqR,hqC,hqO,hqF⟩ := root_limit_at_liminf m hmass (fun n => (hm n).2.1) hfin
  have hqd : d ≤ q.fredholm s := by
    have hb := liminf_le_liminf (f := atTop) (Eventually.of_forall fun n => (hm n).2.2)
    have ht := (hd.comp hα).liminf_eq
    simp only [Function.comp_def] at ht
    rw [ht] at hb
    exact hb.trans (hqF s hs)
  apply (sInf_le ⟨q,⟨hqM,hqR,hqd⟩,rfl⟩ : rootFredholmInfimum s M d ≤ q.cost).trans
  rwa [he] at hqC

end
end jacobi.Variational
