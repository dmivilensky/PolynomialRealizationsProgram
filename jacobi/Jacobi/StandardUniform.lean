import jacobi.Jacobi.StandardKernelLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Uniform convergence of the genuine standard Green kernel away from zero.
The tail-integral kernel is continuous at every positive pair, including
the terminal point one. Compactness then upgrades the proved moving-mesh
limit to the full floor-index uniform statement on each positive square.
Use: StandardJacobi states the exact standard-realization kernel theorem.
Article: jacobi, Theorem 5.4.
Article role: compact uniformity of the Green kernel with the terminal zero convention.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter MeasureTheory chebyshev1.Analysis
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The true inverse-power tail integral is continuous at every
positive starting point, also when that point equals the final endpoint.
Article: jacobi, Theorem 5.4.
-/
theorem standard_tail_continuousAt (a : ℝ) {x : ℝ} (hx : 0<x) :
    ContinuousAt (fun t : ℝ => ∫ v in t..1,1/v^(2*a+1)) x := by
  let g : ℝ → ℝ := fun v => 1/v^(2*a+1)
  have hc (v : ℝ) (hv : 0<v) : ContinuousAt g v :=
    continuousAt_const.div (continuousAt_id.rpow_const (Or.inl hv.ne'))
      (rpow_pos_of_pos hv _).ne'
  have hi : IntervalIntegrable g volume x 1 := by
    apply ContinuousOn.intervalIntegrable
    intro v hv
    exact (hc v ((lt_min hx zero_lt_one).trans_le hv.1)).continuousWithinAt
  have hm : StronglyMeasurable g := by fun_prop
  exact (intervalIntegral.integral_hasDerivAt_left hi hm.stronglyMeasurableAtFilter (hc x hx)).continuousAt

/-- The genuine limit kernel is jointly continuous at every positive
pair. No removable logarithmic formula is needed when a equals zero.
Article: jacobi, Theorem 5.4.
-/
theorem standardLimitKernel_continuousAt (a : ℝ) {s t : ℝ} (hs : 0<s) (ht : 0<t) :
    ContinuousAt (fun p : ℝ×ℝ => standardLimitKernel a p.1 p.2) (s,t) := by
  have h1 : ContinuousAt (fun p : ℝ×ℝ => p.1^(2*a+1)) (s,t) :=
    continuous_fst.continuousAt.rpow_const (Or.inl hs.ne')
  have h2 : ContinuousAt (fun p : ℝ×ℝ => p.2^(2*a+1)) (s,t) :=
    continuous_snd.continuousAt.rpow_const (Or.inl ht.ne')
  have hmax : ContinuousAt (fun p : ℝ×ℝ => max p.1 p.2) (s,t) :=
    continuous_fst.continuousAt.max continuous_snd.continuousAt
  have htail : ContinuousAt (fun p : ℝ×ℝ => ∫ v in max p.1 p.2..1,1/v^(2*a+1)) (s,t) :=
    ContinuousAt.comp (f := fun p : ℝ×ℝ => max p.1 p.2) (x := (s,t))
      (standard_tail_continuousAt a (hs.trans_le (le_max_left s t))) hmax
  exact (continuousAt_const.mul (h1.mul h2).sqrt).mul htail

/-- Full uniform floor-index Green convergence on every closed positive
physical square. The tail formula provides the terminal zero extension,
so the statement includes s=1 or t=1 exactly.
Article: jacobi, Theorem 5.4.
-/
theorem standardGreenTail_uniform {a b : ℝ} (ha : -1<a) (hb : -1<b) {δ : ℝ} (hδ : 0<δ) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ n≥N,∀ s∈Icc δ 1,∀ t∈Icc δ 1,
      |standardGreenTail a b n (Nat.floor ((n:ℝ)*s)) (Nat.floor ((n:ℝ)*t))/(n:ℝ)-
        standardLimitKernel a s t|<ε := by
  classical
  intro ε hε
  by_contra h
  push Not at h
  choose ns hns ss hss ts hts hbad using h
  have hn := tendsto_atTop_mono hns tendsto_id
  obtain ⟨p,hp,φ,hφ,hratio⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq
    (fun k => show (ss k,ts k)∈Icc δ 1 ×ˢ Icc δ 1 from ⟨hss k,hts k⟩)
  have hs : Tendsto (ss ∘ φ) atTop (𝓝 p.1) := continuous_fst.continuousAt.tendsto.comp hratio
  have ht : Tendsto (ts ∘ φ) atTop (𝓝 p.2) := continuous_snd.continuousAt.tendsto.comp hratio
  have hn' := hn.comp hφ.tendsto_atTop
  have hi := floor_mesh_limit hn' hs
    (Eventually.of_forall (fun k => hδ.le.trans (hss (φ k)).1))
  have hj := floor_mesh_limit hn' ht
    (Eventually.of_forall (fun k => hδ.le.trans (hts (φ k)).1))
  have hlim := standardGreenTail_mesh_limit ha hb (ns ∘ φ)
    (fun k => Nat.floor ((ns (φ k):ℝ)*ss (φ k)))
    (fun k => Nat.floor ((ns (φ k):ℝ)*ts (φ k)))
    ⟨hδ.trans_le hp.1.1,hp.1.2⟩ ⟨hδ.trans_le hp.2.1,hp.2.2⟩ hn' hi hj
  have hfun := (standardLimitKernel_continuousAt a (hδ.trans_le hp.1.1)
    (hδ.trans_le hp.2.1)).tendsto.comp (hs.prodMk_nhds ht)
  have herr := hlim.sub hfun
  simp only [sub_self] at herr
  obtain ⟨k,hk⟩ := (herr.norm.eventually
    (Iio_mem_nhds (by simpa only [norm_zero] using hε))).exists
  exact (not_lt_of_ge (hbad (φ k))) hk

end
end jacobi.Jacobi
