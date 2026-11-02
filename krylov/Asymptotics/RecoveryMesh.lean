import krylov.Asymptotics.RecoveryNorm
import krylov.Design.HyperbolicDictionary
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Order.Floor

/-!
Article: main_krylov, thm:limit, admissible mesh and simultaneous limits.
Use: a fixed mesh inflation `c>1` makes the actual recovery strings
spectrally admissible eventually. Letting c decrease to one preserves the
sharp constant, avoiding any numerical inverse or unproved mesh tuning.
The floor grid fills the continuum interval and fits every cycle with
`n theta → infinity`.
Source: the proved physical Gershgorin estimate, elementary limits and
the exact source hyperbolic normalization.
-/

namespace krylov.Asymptotics
noncomputable section
open Real Filter Set
open scoped Topology

/-- The exact source spacing as a function of the positive spectral gap. -/
def gapSpacing (R : ℝ) : ℝ := 2 * arsinh ((sqrt R)⁻¹)

theorem gapSpacing_pos {R : ℝ} (hR : 0 < R) : 0 < gapSpacing R :=
  mul_pos (by norm_num) (arsinh_pos_iff.mpr (inv_pos.mpr (sqrt_pos.mpr hR)))

theorem gapSpacing_eq_designSpacing (I : chebyshev1.SpectralInterval) :
    gapSpacing (I.kappa - 1) = krylov.Design.designSpacing I := by
  rw [gapSpacing, krylov.Design.designSpacing, krylov.Design.sqrt_inverse_kappa_gap]

/-- The source spacing tends to zero for a diverging spectral gap. -/
theorem gapSpacing_tendsto_zero : Tendsto gapSpacing atTop (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have ha := Real.continuous_arsinh.continuousAt.tendsto.comp hi
  change Tendsto (fun R : ℝ ↦ 2 * arsinh ((sqrt R)⁻¹)) atTop (𝓝 0)
  simpa only [Function.comp_def, arsinh_zero, mul_zero] using ha.const_mul 2

/-- The exact leading mesh conversion is two, derived from the actual
derivative of arsinh at zero. -/
theorem gapSpacing_mul_sqrt_tendsto :
    Tendsto (fun R ↦ gapSpacing R * sqrt R) atTop (𝓝 2) := by
  have hi : Tendsto (fun R : ℝ ↦ (sqrt R)⁻¹) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop,
      (eventually_gt_atTop (0 : ℝ)).mono fun R hR ↦ inv_pos.mpr (sqrt_pos.mpr hR)⟩
  have hd := (Real.hasDerivAt_arsinh 0).tendsto_slope_zero_right.comp hi
  have hh : Tendsto (fun R : ℝ ↦ arsinh ((sqrt R)⁻¹) / (sqrt R)⁻¹) atTop (𝓝 1) := by
    simpa [Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
  have he : (fun R : ℝ ↦ gapSpacing R * sqrt R) =
      (fun R ↦ 2 * (arsinh ((sqrt R)⁻¹) / (sqrt R)⁻¹)) := by
    funext R
    simp only [gapSpacing, div_inv_eq_mul]
    ring
  rw [he]
  simpa only [mul_one] using hh.const_mul 2

/-- A genuine fixed inflation above the source spacing gives eventual
spectral admissibility for the exact recovery-radius majorant. -/
theorem inflated_mesh_spectral {α : Type*} {l : Filter α} {R : α → ℝ}
    (hR : Tendsto R l atTop) {c L : ℝ} (hc : 1 < c) :
    ∀ᶠ a in l, 4 * exp (L * (c * gapSpacing (R a))) /
      (c * gapSpacing (R a)) ^ 2 ≤ R a := by
  have hθ : Tendsto (fun a ↦ gapSpacing (R a)) l (𝓝 0) := gapSpacing_tendsto_zero.comp hR
  have he : Tendsto (fun a ↦ 4 * exp (L * (c * gapSpacing (R a)))) l (𝓝 4) := by
    have ha := Real.continuous_exp.continuousAt.tendsto.comp ((hθ.const_mul c).const_mul L)
    simpa only [Function.comp_def, mul_zero, exp_zero, mul_one] using ha.const_mul 4
  have hs : Tendsto (fun a ↦ (c * gapSpacing (R a)) ^ 2 * R a) l (𝓝 (4 * c ^ 2)) := by
    have hh := ((gapSpacing_mul_sqrt_tendsto.comp hR).const_mul c).pow 2
    have heq : (fun a ↦ (c * ((fun R ↦ gapSpacing R * sqrt R) ∘ R) a) ^ 2) =ᶠ[l]
        (fun a ↦ (c * gapSpacing (R a)) ^ 2 * R a) := by
      filter_upwards [hR.eventually (eventually_gt_atTop (0 : ℝ))] with a ha
      dsimp only [Function.comp_apply]
      rw [mul_pow, mul_pow, sq_sqrt ha.le]
      ring
    simpa only [show (c * 2) ^ 2 = 4 * c ^ 2 by ring] using hh.congr' heq
  have hlim := hs.sub he
  have hp : 0 < 4 * c ^ 2 - 4 := by nlinarith
  have hgood := (tendsto_order.1 hlim).1 0 hp
  filter_upwards [hgood, hR.eventually (eventually_gt_atTop (0 : ℝ))] with a ha hRa
  apply (div_le_iff₀ (sq_pos_of_pos (mul_pos (by linarith : 0 < c) (gapSpacing_pos hRa)))).2
  linarith

/-- The true floor grid lies in its prescribed continuum window. -/
theorem floor_mesh_le {Y h : ℝ} (hY : 0 ≤ Y) (hh : 0 < h) :
    (⌊Y / h⌋₊ : ℝ) * h ≤ Y := by
  exact (mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg hY hh.le)) hh.le).trans_eq
    (div_mul_cancel₀ Y hh.ne')

/-- The last grid point is less than one actual mesh width short of the
right endpoint. -/
theorem floor_mesh_lower {Y h : ℝ} (hh : 0 < h) :
    Y - h < (⌊Y / h⌋₊ : ℝ) * h := by
  have he := (mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (Y / h)) hh)
  rw [div_mul_cancel₀ Y hh.ne', add_mul, one_mul] at he
  linarith

/-- Floor meshes really fill the full continuum interval as h tends to zero. -/
theorem floor_mesh_tendsto {α : Type*} {l : Filter α} {h : α → ℝ} {Y : ℝ}
    (hY : 0 ≤ Y) (hh : ∀ᶠ a in l, 0 < h a) (hlim : Tendsto h l (𝓝 0)) :
    Tendsto (fun a ↦ (⌊Y / h a⌋₊ : ℝ) * h a) l (𝓝 Y) := by
  have hlo : Tendsto (fun a ↦ Y - h a) l (𝓝 Y) := by simpa only [sub_zero] using hlim.const_sub Y
  exact hlo.squeeze' tendsto_const_nhds (hh.mono fun a ha ↦ (floor_mesh_lower ha).le)
    (hh.mono fun a ha ↦ floor_mesh_le hY ha)

/-- Any growing type-time cycle budget eventually contains the actual
floor recovery grid on every fixed continuum window. -/
theorem floor_mesh_fits {α : Type*} {l : Filter α} {h : α → ℝ} {n : α → ℕ} {Y : ℝ}
    (hh : ∀ᶠ a in l, 0 < h a) (hn : Tendsto (fun a ↦ (n a : ℝ) * h a) l atTop) :
    ∀ᶠ a in l, ⌊Y / h a⌋₊ ≤ n a := by
  filter_upwards [hh, (tendsto_atTop.1 hn) Y] with a ha hlarge
  exact Nat.floor_le_of_le ((div_le_iff₀ ha).2 hlarge)

/-- Dropping the final atom does not change the simultaneous growing
cycle condition. This keeps the source's `n-1` criterion explicit. -/
theorem preterminal_mesh_diverges {α : Type*} {l : Filter α} {h : α → ℝ} {n : α → ℕ}
    (hh : Tendsto h l (𝓝 0)) (hp : ∀ᶠ a in l, 0 < h a)
    (hn : Tendsto (fun a ↦ (n a : ℝ) * h a) l atTop) :
    Tendsto (fun a ↦ ((n a - 1 : ℕ) : ℝ) * h a) l atTop := by
  apply tendsto_atTop.2
  intro b
  have hsmall := (tendsto_order.1 hh).2 1 zero_lt_one
  filter_upwards [hp, hsmall, (tendsto_atTop.1 hn) (max (b + 1) 1)] with a ha hs hlarge
  have hn₁ : 1 ≤ n a := by
    by_contra h
    have hz : n a = 0 := by omega
    rw [hz, Nat.cast_zero, zero_mul] at hlarge
    linarith [le_max_right (b + 1) 1]
  rw [Nat.cast_sub hn₁, Nat.cast_one, sub_mul, one_mul]
  have hbound := (le_max_left (b + 1) 1).trans hlarge
  linarith

end
end krylov.Asymptotics
