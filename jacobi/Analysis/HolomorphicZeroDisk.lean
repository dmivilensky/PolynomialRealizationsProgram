import jacobi.Analysis.ZeroDisk
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Article: jacobi, Lemma E.1.
The argument uses the community Banach theorem and Weierstrass
limit theorem, without a separate Rouche or monodromy premise.
Use: the original Bessel zero branch discharges the composition property from its actual analytic coefficient series and nonzero Fourier normalization.
-/
namespace jacobi.Analysis
noncomputable section
open Set Metric Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The unique zeros supplied by a uniform genuine complex disk contraction form a holomorphic branch when its actual compositions preserve holomorphy.
Use: the original Bessel zero branch discharges the composition property from its actual analytic coefficient series and nonzero Fourier normalization.
Article: jacobi, Lemma E.1.
Source: Banach's fixed-point theorem and Weierstrass' locally uniform limit theorem.
Proof: start the true iteration z-f(a,z) at zero. The derivative bound keeps every iterate in the original disk, and its actual zero is at distance at most r*2^(-n) from the nth iterate uniformly in a. Every iterate is holomorphic by the genuine composition property. The community locally uniform limit theorem therefore makes the actual unique zero holomorphic. -/
theorem holomorphic_unique_zero_disk {U : Set ℂ} (hU : IsOpen U) {r : ℝ} (hr : 0≤r)
    {f f' : ℂ → ℂ → ℂ}
    (hd : ∀ a∈U,∀ z∈closedBall (0:ℂ) r,HasDerivAt (f a) (f' a z) z)
    (hb : ∀ a∈U,∀ z∈closedBall (0:ℂ) r,‖1-f' a z‖≤1/2)
    (h0 : ∀ a∈U,‖f a 0‖≤r/2)
    (hcomp : ∀ v : ℂ → ℂ,DifferentiableOn ℂ v U →
      (∀ a∈U,‖v a‖≤r) → DifferentiableOn ℂ (fun a => f a (v a)) U) :
    ∃ u : ℂ → ℂ,DifferentiableOn ℂ u U ∧ ∀ a∈U,
      ‖u a‖≤r ∧ f a (u a)=0 ∧ f' a (u a)≠0 ∧
      ∀ z : ℂ,‖z‖≤r → f a z=0 → z=u a := by
  -- The root is chosen from the actual pointwise theorem; uniform iteration then proves its holomorphy.
  classical
  have hex (a : ℂ) (ha : a∈U) := unique_simple_zero_disk hr (hd a ha) (hb a ha) (h0 a ha)
  let u (a : ℂ) : ℂ := if ha : a∈U then Classical.choose (hex a ha) else 0
  have hu (a : ℂ) (ha : a∈U) : ‖u a‖≤r ∧ f a (u a)=0 ∧ f' a (u a)≠0 ∧
      ∀ z : ℂ,‖z‖≤r → f a z=0 → z=u a := by
    have hh := Classical.choose_spec (hex a ha)
    simpa only [u,dite_eq_left ha] using And.intro hh.1 (And.intro hh.2.1 (And.intro hh.2.2.2.1 hh.2.2.2.2))
  let G (a z : ℂ) : ℂ := z-f a z
  have hLip (a : ℂ) (ha : a∈U) : LipschitzOnWith (1/2:NNReal) (G a) (closedBall 0 r) :=
    (convex_closedBall (0:ℂ) r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => ((hasDerivAt_id z).sub (hd a ha z hz)).hasDerivWithinAt)
      (fun z hz => by exact_mod_cast hb a ha z hz)
  have hmem : (0:ℂ)∈closedBall (0:ℂ) r := by simpa only [mem_closedBall,dist_self] using hr
  have hmaps (a : ℂ) (ha : a∈U) : MapsTo (G a) (closedBall 0 r) (closedBall 0 r) := by
    intro z hz
    have hh := (hLip a ha).norm_sub_le hz hmem
    have hn : ‖z‖≤r := by simpa only [mem_closedBall,dist_zero_right] using hz
    have hG : ‖G a 0‖=‖f a 0‖ := by simp [G]
    have ht := norm_le_norm_sub_add (G a z) (G a 0)
    rw [hG] at ht
    simp only [sub_zero,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] at hh
    rw [mem_closedBall,dist_zero_right]
    linarith [h0 a ha]
  let v (n : ℕ) (a : ℂ) : ℂ := (G a)^[n] 0
  have hv (n : ℕ) (a : ℂ) (ha : a∈U) : v n a∈closedBall (0:ℂ) r :=
    (hmaps a ha).iterate n hmem
  have hiter (n : ℕ) : DifferentiableOn ℂ (v n) U := by
    induction n with
    | zero => exact differentiableOn_const 0
    | succ n ih =>
      have hh := ih.sub (hcomp (v n) ih (fun a ha => by
        simpa only [mem_closedBall,dist_zero_right] using hv n a ha))
      convert! hh using 1
      ext a
      simp only [v,Function.iterate_succ_apply',G,Pi.sub_apply]
  have hdist (n : ℕ) (a : ℂ) (ha : a∈U) : dist (u a) (v n a)≤r*(1/2:ℝ)^n := by
    induction n with
    | zero => simpa only [v,Function.iterate_zero,id_eq,dist_zero_right,pow_zero,mul_one] using (hu a ha).1
    | succ n ih =>
      have huf : G a (u a)=u a := by dsimp [G]; rw [(hu a ha).2.1,sub_zero]
      have humem : u a∈closedBall (0:ℂ) r := by simpa only [mem_closedBall,dist_zero_right] using (hu a ha).1
      have hh := (hLip a ha).dist_le_mul (u a) humem (v n a) (hv n a ha)
      rw [huf] at hh
      have hvstep : v (n+1) a=G a (v n a) := Function.iterate_succ_apply' (G a) n 0
      rw [hvstep]
      exact hh.trans ((mul_le_mul_of_nonneg_left ih (by norm_num : (0:ℝ)≤1/2)).trans_eq (by ring))
  have hlim : Tendsto (fun n : ℕ => r*(1/2:ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1)).const_mul r
  have hconv : TendstoUniformlyOn v u atTop U := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hlim.eventually_lt_const hε] with n hn a ha
    exact (hdist n a ha).trans_lt hn
  refine ⟨u,hconv.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall hiter) hU,hu⟩

end
end jacobi.Analysis
