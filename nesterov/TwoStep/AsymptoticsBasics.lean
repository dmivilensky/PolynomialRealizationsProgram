import nesterov.Momentum.Parameters
import nesterov.Quadratic.Price
import nesterov.Quadratic.ScaledJury
import nesterov.Flow.Constants

/-! Quantitative consequences of accelerated quadratic convergence.
All rates here are the actual maxima over curvatures and characteristic roots. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

/-- Closed-circle endpoint signs, obtained from the strict scaled Jury test. -/
theorem roots_le_radius_signs {a q r : ℝ} (hr : 0≤r)
    (hroot : ∀ z : ℂ,z^2-(a:ℂ)*z+(q:ℂ)=0 → ‖z‖≤r) :
    0≤r^2-a*r+q ∧ 0≤r^2+a*r+q := by
  have hs : ∀ᶠ s in 𝓝[>] r,0<s^2-a*s+q ∧ 0<s^2+a*s+q := by
    filter_upwards [self_mem_nhdsWithin] with s hsr
    have hs : 0<s := hr.trans_lt hsr
    exact ((Quadratic.roots_lt_radius_iff hs).mp (fun z hz=>(hroot z hz).trans_lt hsr)).2
  have hp : Tendsto (fun s : ℝ=>s^2-a*s+q) (𝓝[>] r) (𝓝 (r^2-a*r+q)) := by
    exact (by fun_prop : Continuous (fun s : ℝ=>s^2-a*s+q)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hm : Tendsto (fun s : ℝ=>s^2+a*s+q) (𝓝[>] r) (𝓝 (r^2+a*r+q)) := by
    exact (by fun_prop : Continuous (fun s : ℝ=>s^2+a*s+q)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact ⟨ge_of_tendsto hp (hs.mono fun _ h=>h.1.le),
    ge_of_tendsto hm (hs.mono fun _ h=>h.2.le)⟩

/-- Lemma accel(a): the physical parameters stay in explicit bounded sets. -/
theorem accelerated_tuning_bounds (q : Momentum.Tuning) {ε c : ℝ}
    (hε : 0<ε) (hε1 : ε<1) (hc : 0<c) (hstable : q.Stable (ε^2) 1)
    (hrate : Quadratic.quadraticRate (ε^2) 1 q.beta q.tau q.stepSize≤1-c*ε) :
    c^2≤q.stepSize ∧ q.stepSize<4 ∧ q.tau<2/c^2 ∧
      1-q.beta<max 4 (8/c)*ε := by
  have hμ : 0<ε^2 := sq_pos_of_pos hε
  have hμL : ε^2<1 := by nlinarith
  let ρ := Quadratic.quadraticRate (ε^2) 1 q.beta q.tau q.stepSize
  have hρ : 0≤ρ := Quadratic.quadraticRate_nonneg_general hμL.le
  have hgap : c*ε≤1-ρ := by dsimp [ρ];linarith
  have hgap0 : 0≤1-ρ := (mul_pos hc hε).le.trans hgap
  obtain ⟨hfirst,_,_⟩ := Quadratic.endpoint_rate_bounds hμL.le hstable
  have hy : c^2≤q.stepSize := by
    have hh : (c*ε)^2≤(1-ρ)^2 :=
      (sq_le_sq₀ (mul_nonneg hc.le hε.le) hgap0).mpr hgap
    dsimp [ρ] at hh
    apply (mul_le_mul_iff_of_pos_right hμ).mp
    nlinarith
  have hmargin := (q.stable_iff hμ hμL).mp hstable
  simp only [mul_one] at hmargin
  have hy4 : q.stepSize<4 := by
    nlinarith [mul_nonneg q.step_pos.le q.tau_nonneg,q.beta_lt_one]
  have hτ : q.tau<2/c^2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hc)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hy q.tau_nonneg,q.beta_lt_one,q.step_pos]
  have hr : 0≤1-c*ε := hρ.trans hrate
  have hroots (z : ℂ)
      (hz : z^2-(Quadratic.S q.beta q.tau q.stepSize (ε^2):ℂ)*z+
        (Quadratic.Q q.beta q.tau q.stepSize (ε^2):ℂ)=0) : ‖z‖≤1-c*ε := by
    exact (Quadratic.root_norm_le_rate_general hμL.le ⟨le_rfl,hμL.le⟩
      (by rwa [Quadratic.characteristic_eq])).trans hrate
  have hp := (roots_le_radius_signs hr hroots).1
  dsimp [Quadratic.S,Quadratic.Q] at hp
  have hbound : c*(1-q.beta)≤(c^2+q.stepSize)*ε := by
    have hn := mul_nonneg (mul_nonneg (mul_nonneg q.step_pos.le hμ.le)
      (show 0≤1+q.tau by linarith [q.tau_nonneg]))
      (mul_nonneg hc.le hε.le)
    apply (mul_le_mul_iff_of_pos_right hε).mp
    nlinarith
  have hc2 : c^2<4 := hy.trans_lt hy4
  have hcfin : c*(1-q.beta)<8*ε := by
    have hh : (c^2+q.stepSize)*ε<8*ε := mul_lt_mul_of_pos_right (by linarith) hε
    exact hbound.trans_lt hh
  have hβ : 1-q.beta<(8/c)*ε := by
    have hh : 1-q.beta<8*ε/c := (lt_div_iff₀ hc).mpr (by nlinarith [hcfin])
    convert hh using 1
    ring
  exact ⟨hy,hy4,hτ,hβ.trans_le (mul_le_mul_of_nonneg_right (le_max_right 4 (8/c)) hε.le)⟩

end
end nesterov.TwoStep
