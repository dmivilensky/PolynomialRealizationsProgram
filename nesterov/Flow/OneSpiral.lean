import nesterov.Flow.OrbitInterpolation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: Proposition `one`, the first-return obstruction in Appendix B.
Use: the minimizer requires arbitrarily fast winding near θ/3, while the
first angular return places a finite upper bound on a single frequency.
-/

noncomputable section

namespace nesterov.Flow

open Filter
open scoped Topology

def OneAtomFeasible (θ m c γ : ℝ) : Prop :=
  (∀ q : ℝ, 0 < q → 0 ≤ forwardKernel θ m c γ q) ∧
  (∀ q : ℝ, 0 < q → 0 ≤ backwardKernel θ m c γ q) ∧
  c * delta θ m c ≤ (3 * c - θ) * γ ^ 2

theorem sinh_le_mul_cosh {u : ℝ} (hu : 0 ≤ u) : Real.sinh u ≤ u * Real.cosh u := by
  have hd (t : ℝ) : HasDerivAt (fun s => s * Real.cosh s - Real.sinh s)
      (t * Real.sinh t) t := by
    convert (((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hm : MonotoneOn (fun s => s * Real.cosh s - Real.sinh s) (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).hasDerivWithinAt
    · intro t ht
      exact mul_nonneg (interior_subset ht) (Real.sinh_nonneg_iff.mpr (interior_subset ht))
  have hh := hm (by simp : (0 : ℝ) ∈ Set.Ici 0) hu hu
  simp only [zero_mul, Real.sinh_zero, sub_self] at hh
  linarith

theorem cosh_sub_one_le_half_mul_sinh {v : ℝ} (hv : 0 ≤ v) :
    Real.cosh v - 1 ≤ v / 2 * Real.sinh v := by
  have hh := sinh_le_mul_cosh (show 0 ≤ v / 2 by linarith)
  have hn := Real.sinh_nonneg_iff.mpr (show 0 ≤ v / 2 by linarith)
  have hc := Real.cosh_sq_sub_sinh_sq (v / 2)
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * Real.sinh (v / 2) by positivity)
  have he : v = 2 * (v / 2) := by ring
  have hcos : Real.cosh v = Real.cosh (v / 2) ^ 2 + Real.sinh (v / 2) ^ 2 := by
    calc
      _ = Real.cosh (2 * (v / 2)) := congrArg Real.cosh he
      _ = _ := Real.cosh_two_mul (v / 2)
  have hsin : Real.sinh v = 2 * Real.sinh (v / 2) * Real.cosh (v / 2) := by
    calc
      _ = Real.sinh (2 * (v / 2)) := congrArg Real.sinh he
      _ = _ := Real.sinh_two_mul (v / 2)
  rw [hcos, hsin]
  nlinarith

/-- Convexity at the first complete angular return bounds a single winding. -/
theorem oneAtom_frequency_upper {θ m c γ : ℝ} (hc : 0 < c)
    (hct : c < θ / 2) (hd : 0 < delta θ m c) (hγ : 0 < γ)
    (h : OneAtomFeasible θ m c γ) : γ ≤ Real.pi * c ^ 2 / (θ - 2 * c) := by
  let q := 2 * Real.pi / γ
  let v := c * q
  have hq : 0 < q := by dsimp [q]; positivity
  have hv : 0 < v := mul_pos hc hq
  have hlag := h.1 q hq
  have hγq : γ * q = 2 * Real.pi := by dsimp [q]; field_simp
  dsimp [forwardKernel, kernelA, kernelB] at hlag
  rw [hγq, Real.cos_two_pi, Real.sin_two_pi, sub_zero] at hlag
  change 0 ≤ (γ ^ 2 - delta θ m c) * (Real.cosh v - 1) -
    (θ - 2 * c) * γ * (γ * Real.sinh v / c) at hlag
  have hs : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hv
  have ha : 0 ≤ Real.cosh v - 1 := by linarith [Real.one_le_cosh v]
  have hcoeff : 0 < θ - 2 * c := by linarith
  have hmargin := cosh_sub_one_le_half_mul_sinh hv.le
  have hfirst : (θ - 2 * c) * γ * (γ * Real.sinh v / c) ≤
      γ ^ 2 * (v / 2 * Real.sinh v) := by
    have hh := mul_le_mul_of_nonneg_left hmargin (sq_nonneg γ)
    have hh' := mul_nonneg hd.le ha
    nlinarith
  have hmul : (θ - 2 * c) / c ≤ v / 2 := by
    apply le_of_mul_le_mul_right _ (mul_pos (sq_pos_of_pos hγ) hs)
    convert hfirst using 1 <;> simp only [div_eq_mul_inv] <;> ring
  have hvq : v / 2 = Real.pi * c / γ := by dsimp [v, q]; field_simp
  rw [hvq] at hmul
  have hh := (div_le_div_iff₀ hc hγ).mp hmul
  apply (le_div_iff₀ hcoeff).mpr
  nlinarith

/-- Proposition one: no one-frequency program works in a whole interval
immediately above θ/3.  The endpoint c_sharp is strictly below cQ. -/
theorem exists_oneAtom_obstruction {θ m : ℝ} (hθ : 0 < θ) (_hm : 0 < m)
    (hgap : θ / 3 < cQ θ m) :
    ∃ csharp : ℝ, θ / 3 < csharp ∧ csharp < cQ θ m ∧
      ∀ c γ : ℝ, θ / 3 < c → c ≤ csharp → 0 ≤ γ → ¬OneAtomFeasible θ m c γ := by
  let a := θ / 3
  have ha : 0 < a := by dsimp [a]; linarith
  have hd : 0 < delta θ m a := ((lt_cQ_iff θ m a).mp hgap).2
  let F : ℝ → ℝ := fun c => c * delta θ m c -
    (3 * c - θ) * (Real.pi * c ^ 2 / (θ - 2 * c)) ^ 2
  have hden : θ - 2 * a ≠ 0 := by dsimp [a]; linarith
  have hcont : ContinuousAt F a := by
    dsimp [F, delta]
    fun_prop
  have hFa : 0 < F a := by
    have he : 3 * a - θ = 0 := by dsimp [a]; ring
    dsimp [F]
    rw [he, zero_mul, sub_zero]
    exact mul_pos ha hd
  have hev : ∀ᶠ c in 𝓝 a, 0 < F c := hcont.eventually (eventually_gt_nhds hFa)
  obtain ⟨r, hr, hrF⟩ := Metric.eventually_nhds_iff.mp hev
  let d := min (r / 2) ((cQ θ m - a) / 2)
  have hdpos : 0 < d := lt_min (by linarith) (by dsimp [a]; linarith)
  refine ⟨a + d, ?_, ?_, ?_⟩
  · change a < a + d
    linarith
  · have hh := min_le_right (r / 2) ((cQ θ m - a) / 2)
    dsimp [d] at *
    dsimp [a] at *
    linarith
  · intro c γ hac hcap hγ hfeas
    have hc : 0 < c := by dsimp [a] at ha; linarith
    have hcQ : c < cQ θ m := by
      have hh := min_le_right (r / 2) ((cQ θ m - a) / 2)
      dsimp [d] at *
      dsimp [a] at *
      linarith
    obtain ⟨hct, hdelta⟩ := (lt_cQ_iff θ m c).mp hcQ
    have hγp : 0 < γ := by
      by_contra hγp
      have hz : γ = 0 := le_antisymm (le_of_not_gt hγp) hγ
      have hh := hfeas.2.2
      rw [hz] at hh
      have hp := mul_pos hc hdelta
      nlinarith
    have hupper := oneAtom_frequency_upper hc hct hdelta hγp hfeas
    have hF : 0 < F c := by
      apply hrF
      rw [Real.dist_eq, abs_of_nonneg (show 0 ≤ c - a by dsimp [a]; linarith)]
      have hh := min_le_left (r / 2) ((cQ θ m - a) / 2)
      dsimp [d] at *
      linarith
    have hdenpos : 0 < θ - 2 * c := by linarith
    have hU : 0 ≤ Real.pi * c ^ 2 / (θ - 2 * c) := by positivity
    have hsq := (sq_le_sq₀ hγ hU).mpr hupper
    have hcoef : 0 ≤ 3 * c - θ := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsq hcoef
    have hmin := hfeas.2.2
    dsimp [F] at hF
    linarith

end nesterov.Flow
