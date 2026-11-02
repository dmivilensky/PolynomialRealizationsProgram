import jacobi.Analytic.BesselOrderContinuity

/-!
Article: jacobi, Lemma E.1.
This is the input for holomorphic iterations constructing the
uniform complex-order zero branches.
Use: the original Bessel zero-disk fixed-point iterates are holomorphic even though both the actual order and frequency change at every iteration.
-/
namespace jacobi.Bessel
noncomputable section
open Complex Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original normalized Bessel function is analytic along every genuine analytic order-and-energy curve in its admissible half-plane.
Use: the original Bessel zero-disk fixed-point iterates are holomorphic even though both the actual order and frequency change at every iteration.
Article: jacobi, Lemma E.1.
Source: Weierstrass' theorem applied to the original Bessel coefficient series, DLMF 10.2.2.
Proof: keep a positive order margin and a bounded spectral argument on one actual parameter neighborhood. Every original coefficient term is analytic there and the genuine common factorial majorant is summable. The community holomorphic-series theorem identifies the analytic sum with the original normalized Bessel function. -/
theorem normalized_comp_analytic {A Z : ℂ → ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ A p) (hZ : AnalyticAt ℂ Z p) (hp : -1<(A p).re) :
    AnalyticAt ℂ (fun u => normalized (A u) (Z u)) p := by
  -- The same original locally bounded series controls both moving Bessel arguments.
  let δ : ℝ := ((A p).re+1)/2
  let R : ℝ := ‖Z p‖+1
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hmargin : ∀ᶠ u in 𝓝 p,δ<(A u).re+1 := by
    apply ((Complex.continuous_re.continuousAt.comp hA.continuousAt).add_const 1).eventually_const_lt
    dsimp [δ]
    linarith
  have hradius : ∀ᶠ u in 𝓝 p,‖Z u‖<R :=
    hZ.continuousAt.norm.eventually_lt_const (by dsimp [R]; linarith)
  obtain ⟨U,hUsub,hUopen,hpU⟩ := eventually_nhds_iff.mp
    ((hA.eventually_analyticAt.and hZ.eventually_analyticAt).and (hmargin.and hradius))
  have hterms (n : ℕ) : DifferentiableOn ℂ (fun u => coefficient (A u) n*(Z u)^n) U := by
    intro u hu
    obtain ⟨⟨hAu,hZu⟩,hmu,hru⟩ := hUsub u hu
    have hreal : -1<(A u).re := by linarith
    exact (((coefficient_order_analytic hreal n).comp hAu).mul (hZu.pow n)).differentiableAt.differentiableWithinAt
  have hbound (n : ℕ) (u : ℂ) (hu : u∈U) :
      ‖coefficient (A u) n*(Z u)^n‖≤(R/(4*δ))^n/(n.factorial:ℝ) :=
    normalized_joint_majorant hδ (hUsub u hu).2.1.le (hUsub u hu).2.2.le n
  have hh := Complex.differentiableOn_tsum_of_summable_norm
    (Real.summable_pow_div_factorial (R/(4*δ))) hterms hUopen hbound
  simp_rw [← normalized_eq_tsum] at hh
  exact hh.analyticOnNhd hUopen p hpU

end
end jacobi.Bessel
