import polyak.ModeLocking.TwoLag.Hermite
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Analytic.Polynomial

/-! The slopes in the Hermite system are consequences of global tangency,
not extra data supplied by a numerical computation. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Set Filter
open scoped Topology

theorem analyticAt_W (K : ℕ) (c : ℝ) : AnalyticAt ℝ (W K) c :=
  (AnalyticOnNhd.eval_polynomial (Wpoly K)) c (mem_univ c)

theorem analyticAt_Psi (K : ℕ) {r c : ℝ} (hr : 0≤r) (hc : c∈Icc (-1 : ℝ) 1) :
    AnalyticAt ℝ (Psi K r) c := by
  have hu : AnalyticAt ℝ (Spectral.chebU (K-1)) c :=
    (AnalyticOnNhd.eval_polynomial (Polynomial.Chebyshev.U ℝ ((K-1 : ℕ) : ℤ))) c (mem_univ c)
  exact ((analyticAt_const.add analyticAt_id).mul
    (analyticAt_const.sub (analyticAt_const.mul hu))).div
      (analyticAt_const.add (analyticAt_const.mul (analyticAt_W K c)))
      (Psi_den_pos K hr hc).ne'

theorem contact_slopes (q : Tuning) (K : ℕ) {r c : ℝ} (hr : 0≤r)
    (hc : c∈Ioo (-1 : ℝ) 1)
    (hbound : ∀ x∈Icc (-1 : ℝ) 1, q.Xi x≤Psi K r x)
    (heq : q.Xi c=Psi K r c) : deriv q.Xi c=deriv (Psi K r) c := by
  have hm : IsLocalMin (fun x=>Psi K r x-q.Xi x) c := by
    filter_upwards [Ioo_mem_nhds hc.1 hc.2] with x hx
    rw [← heq, sub_self]
    exact sub_nonneg.mpr (hbound x ⟨hx.1.le, hx.2.le⟩)
  have hd := hm.deriv_eq_zero
  have hder := ((analyticAt_Psi K hr ⟨hc.1.le, hc.2.le⟩).differentiableAt.hasDerivAt.sub
    (Xi_hasDerivAt q c)).deriv
  change deriv (Psi K r-q.Xi) c=0 at hd
  rw [hd] at hder
  rw [(Xi_hasDerivAt q c).deriv]
  linarith

/-- Literal all-degree equation `G_K(r)=0` from the double touching geometry. -/
theorem G_eq_zero_of_global_contact (q : Tuning) (K : ℕ) {r c₁ c₂ : ℝ} (hr : 0≤r)
    (hc₁ : c₁∈Ioo (-1 : ℝ) 1) (hc₂ : c₂∈Ioo (-1 : ℝ) 1) (hc : c₁≠c₂)
    (hbound : ∀ x∈Icc (-1 : ℝ) 1, q.Xi x≤Psi K r x)
    (heq₁ : q.Xi c₁=Psi K r c₁) (heq₂ : q.Xi c₂=Psi K r c₂) :
    G K r c₁ c₂=0 :=
  G_eq_zero q K r hc heq₁ heq₂ (contact_slopes q K hr hc₁ hbound heq₁)
    (contact_slopes q K hr hc₂ hbound heq₂)

end polyak.ModeLocking.TwoLag
