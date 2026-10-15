import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic

/-!
Article: 2606.16671v2, Theorem E.3.
Mesh Approximation.
Use: `«2606.16671v2».Analysis.floor_unit_bounds` feeds
`«2606.16671v2».SineJacobi.convolutionStep_bound` (One integrable bound controls both hard endpoints
of the convolution).
Proof chain: `«2606.16671v2».SineJacobi.convolutionIntegral_limit` — 2606.16671v2, Theorem E.3;
Hard-edge recurrence, singular ODE, uniqueness and endpoint limits.
Source: mathlib, Mathlib.Analysis.SpecificLimits.Basic, Mathlib.Algebra.Order.Floor.Semiring —
convergence of floor meshes. The needed form is proved here.
-/
namespace «2606.16671v2».Analysis
noncomputable section
open Real Set Filter Topology

/--
The stated quantitative bound `|(Nat.floor ((N:ℝ)*x):ℝ)/(N:ℝ)-x| ≤ 1/(N:ℝ)`.

Use: `«2606.16671v2».Analysis.floor_mesh_limit` uses this bound to establish convergence along
the specified source filter to the specified limit: `Tendsto (fun a => (Nat.floor ((N a:ℝ)*x
a):ℝ)/(N a:ℝ)) l (𝓝 t)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecificLimits.Basic, Mathlib.Algebra.Order.Floor.Semiring —
convergence of floor meshes.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem floor_mesh_error {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : 0 ≤ x) :
    |(Nat.floor ((N:ℝ)*x):ℝ)/(N:ℝ)-x| ≤ 1/(N:ℝ) := by
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have h := Nat.abs_floor_sub_le (mul_nonneg hNr.le hx)
  have he : (Nat.floor ((N:ℝ)*x):ℝ)/(N:ℝ)-x =
      ((Nat.floor ((N:ℝ)*x):ℝ)-(N:ℝ)*x)/(N:ℝ) := by field_simp
  rw [he, abs_div, abs_of_pos hNr]
  exact div_le_div_of_nonneg_right h hNr.le

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun a =>
(Nat.floor ((N a:ℝ)*x a):ℝ)/(N a:ℝ)) l (𝓝 t)`.

Use: `«2606.16671v2».SineJacobi.convolutionStep_limit` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun a => convolutionStep (N
a) (s a) x) l (𝓝 (convolutionKernel t x))`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecificLimits.Basic, Mathlib.Algebra.Order.Floor.Semiring —
convergence of floor meshes.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem floor_mesh_limit {α : Type*} {l : Filter α} {N : α → ℕ} {x : α → ℝ} {t : ℝ}
    (hN : Tendsto N l atTop) (hx : Tendsto x l (𝓝 t))
    (hp : ∀ᶠ a in l, 0 ≤ x a) :
    Tendsto (fun a => (Nat.floor ((N a:ℝ)*x a):ℝ)/(N a:ℝ)) l (𝓝 t) := by
  -- Record the convergence he with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have he : Tendsto (fun a => (Nat.floor ((N a:ℝ)*x a):ℝ)/(N a:ℝ)-x a) l (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ) |>.comp hN)
    filter_upwards [hN.eventually_gt_atTop 0, hp] with a hna hxa
    simpa only [Real.norm_eq_abs, Function.comp_def] using floor_mesh_error hna hxa
  simpa only [sub_add_cancel, zero_add] using he.add hx

/--
The precise assertion is `let k`.

Use: `«2606.16671v2».SineJacobi.convolutionStep_bound` uses this assertion to establish the
stated quantitative bound `0 ≤ convolutionStep N s x ∧ convolutionStep N s x ≤ (1/sinc
(Real.pi*b))^2*«2606.16671v2».Analysis.arcsineBound x`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.Analysis.SpecificLimits.Basic, Mathlib.Algebra.Order.Floor.Semiring —
convergence of floor meshes.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem floor_unit_bounds (M : ℕ) (hM : 0 < M) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    let k := Nat.floor ((M:ℝ)*x)
    k < M ∧ (k:ℝ) ≤ (M:ℝ)*x ∧ (M:ℝ)*x < (k:ℝ)+1 := by
  dsimp
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hM
  refine ⟨?_, Nat.floor_le (mul_pos hMr hx.1).le, Nat.lt_floor_add_one _⟩
  apply (Nat.floor_lt (mul_pos hMr hx.1).le).mpr
  nlinarith [hx.2]

end
end «2606.16671v2».Analysis
