import jacobi.Hankel.ZeroDisks
import jacobi.Analytic.BesselComposition
import jacobi.Analysis.HolomorphicZeroDisk

/-!
Article: jacobi, Lemma E.1.
Use: uniform_bessel_holomorphic_zero_disks discharges the holomorphic-composition premise of the actual uniform contraction theorem.
-/
namespace jacobi.Hankel
noncomputable section
open Set Metric
set_option backward.isDefEq.respectTransparency false

/-- The actual original Bessel disk equation is analytic along every analytic frequency displacement whose genuine frequency stays in the slit plane.
Use: uniform_bessel_holomorphic_zero_disks discharges the holomorphic-composition premise of the actual uniform contraction theorem.
Article: jacobi, Lemma E.1.
Proof: the original normalized Bessel coefficient series is analytic along the true moving order-and-energy curve. The original Liouville logarithm is analytic in the actual slit plane, and both genuine nonzero normalizing factors are analytic in the same order neighborhood. -/
theorem frequencyZeroEquation_comp_analytic {R : ℝ} (hR : 0<R) {a : ℂ} (ha : -1<a.re)
    (hc : ‖besselCoefficient a‖/R<1) (hA : outgoingBesselCoefficient hR a≠0)
    (k : ℕ) {v : ℂ → ℂ} (hv : AnalyticAt ℂ v a)
    (hz : frequencyGrid a k+v a∈Complex.slitPlane) :
    AnalyticAt ℂ (fun b => frequencyZeroEquation hR b k (v b)) a := by
  -- The original two Bessel arguments move together in the genuine analytic coefficient series.
  have hq : AnalyticAt ℂ (fun b => frequencyGrid b k) a := by unfold frequencyGrid; fun_prop
  have hzeta := hq.add hv
  have hF := jacobi.Bessel.normalized_comp_analytic (analyticAt_id (𝕜 := ℂ)) (hzeta.pow 2) ha
  have hid : AnalyticAt ℂ (fun b : ℂ => b) a := analyticAt_id
  have hL : AnalyticAt ℂ (fun b : ℂ => frequencyFactor b (frequencyGrid b k+v b)) a := by
    unfold frequencyFactor
    exact (((hid.add (analyticAt_const (v := (1/2:ℂ)))).mul (hzeta.clog hz)).cexp)
  have hN : AnalyticAt ℂ (fun b => frequencyNormalizer b k) a := by
    unfold frequencyNormalizer frequencyGrid
    fun_prop
  exact (((hL.mul hF).div (outgoingBesselCoefficient_analytic hR ha hc) hA).div hN
    (frequencyNormalizer_ne_zero a k))

/-- All genuine sufficiently large Bessel frequency-disk zeros form holomorphic branches on a single complex-order disk, with original uniqueness and simplicity retained.
Use: Lemma E.1's numbered tail is obtained by identifying these actual branches with the original real numbered zeros and refining their actual displacement estimates.
Article: jacobi, Lemma E.1.
Proof: use the already discharged actual uniform Bessel disk derivative and center bounds. Its original half-contraction makes the genuine outgoing coefficient analytic. Every true zero-disk iterate is holomorphic by the actual Bessel composition theorem. The independently proved uniform holomorphic contraction theorem supplies the original branches simultaneously on the same order disk. -/
theorem uniform_bessel_holomorphic_zero_disks {a0 : ℝ} (ha0 : -1<a0) :
    ∃ R r : ℝ,∃ hR : 0<R,∃ N : ℕ,0<r ∧ r≤1 ∧ r<a0+1 ∧ 1≤N ∧
      ∀ k : ℕ,N≤k → ∃ u : ℂ → ℂ,
        DifferentiableOn ℂ u (ball (a0:ℂ) r) ∧
        ∀ a : ℂ,‖a-(a0:ℂ)‖<r → ‖u a‖≤1/4 ∧
          jacobi.Bessel.normalized a ((frequencyGrid a k+u a)^2)=0 ∧
          frequencyZeroSlope hR a k (u a)≠0 ∧
          ∀ ζ : ℂ,‖ζ‖≤1/4 → jacobi.Bessel.normalized a ((frequencyGrid a k+ζ)^2)=0 → ζ=u a := by
  -- The same common disk and cutoff serve every original large spectral index.
  obtain ⟨R,r,hR,N,hr,hr1,hra,hN,hdata⟩ := uniform_bessel_zero_disk_bounds ha0
  refine ⟨R,r,hR,N,hr,hr1,hra,hN,fun k hk => ?_⟩
  let U : Set ℂ := ball (a0:ℂ) r
  have hmem (a : ℂ) : a∈U ↔ ‖a-(a0:ℂ)‖<r := by simp only [U,mem_ball,dist_eq_norm]
  have hd (a : ℂ) (ha : a∈U) (ζ : ℂ) (hζ : ζ∈closedBall (0:ℂ) (1/4)) :=
    ((hdata a ((hmem a).mp ha)).2.2.2 k hk).1 ζ hζ
  have hcomp (v : ℂ → ℂ) (hv : DifferentiableOn ℂ v U) (hvbound : ∀ a∈U,‖v a‖≤1/4) :
      DifferentiableOn ℂ (fun a => frequencyZeroEquation hR a k (v a)) U := by
    intro a ha
    obtain ⟨hc,hreal,hA,_⟩ := hdata a ((hmem a).mp ha)
    have hgrid := (frequencyGrid_disk_geometry ((hmem a).mp ha) hr1 hreal k (hvbound a ha)).1
    have hk1 : 1≤(k:ℝ) := by exact_mod_cast hN.trans hk
    have hslit : frequencyGrid a k+v a∈Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le zero_lt_one (hk1.trans hgrid)))
    exact (frequencyZeroEquation_comp_analytic hR hreal (hc.trans_lt (by norm_num)) hA k
      (hv.analyticOnNhd isOpen_ball a ha) hslit).differentiableAt.differentiableWithinAt
  obtain ⟨u,hu,hroot⟩ := jacobi.Analysis.holomorphic_unique_zero_disk isOpen_ball
    (by norm_num : (0:ℝ)≤1/4) (f := fun a => frequencyZeroEquation hR a k) (f' := fun a => frequencyZeroSlope hR a k)
    (fun a ha ζ hζ => (hd a ha ζ hζ).1) (fun a ha ζ hζ => (hd a ha ζ hζ).2)
    (fun a ha => ((hdata a ((hmem a).mp ha)).2.2.2 k hk).2) hcomp
  refine ⟨u,hu,fun a ha => ?_⟩
  obtain ⟨hsize,hzero,hsimple,hunique⟩ := hroot a ((hmem a).mpr ha)
  have hA := (hdata a ha).2.2.1
  exact ⟨hsize,(frequencyZeroEquation_zero_iff hR hA k (u a)).mp hzero,hsimple,
    fun ζ hζ he => hunique ζ hζ ((frequencyZeroEquation_zero_iff hR hA k ζ).mpr he)⟩

end
end jacobi.Hankel
