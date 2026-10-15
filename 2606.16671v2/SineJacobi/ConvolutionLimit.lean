import «2606.16671v2».SineJacobi.ConvolutionKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Article: 2606.16671v2, Theorem E.3.
The convolution limit includes both singular endpoints, by dominated convergence.
Use: `«2606.16671v2».SineJacobi.convolutionIntegral_limit` feeds
`«2606.16671v2».SineJacobi.endpoint_scaled_limit` (Direct endpoint asymptotics with the exact
normalization of E.3).
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Set Filter Topology MeasureTheory

/--
Defines `convolutionIntegral` of type `ℝ` by `∫ x in (0:ℝ)..1, convolutionKernel t x`.

Use: `«2606.16671v2».SineJacobi.convolutionIntegral_limit` uses this definition to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun a => ∫ x in
(0:ℝ)..1, convolutionStep (N a) (s a) x) l (𝓝 (convolutionIntegral t))`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.
-/
def convolutionIntegral (t : ℝ) : ℝ := ∫ x in (0:ℝ)..1, convolutionKernel t x

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun a =>
convolutionStep (N a) (s a) x) l (𝓝 (convolutionKernel t x))`.

Use: `«2606.16671v2».SineJacobi.convolutionIntegral_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun a => ∫ x in
(0:ℝ)..1, convolutionStep (N a) (s a) x) l (𝓝 (convolutionIntegral t))`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity. Prove equality of functions by
evaluating both sides at an arbitrary argument.
-/
theorem convolutionStep_limit {α : Type*} {l : Filter α} {N s : α → ℕ} {t : ℝ}
    (hN : Tendsto N l atTop) (ht : t ∈ Ioo (0:ℝ) 1)
    (hs : Tendsto (fun a => (s a:ℝ)/(N a:ℝ)) l (𝓝 t))
    {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    Tendsto (fun a => convolutionStep (N a) (s a) x) l (𝓝 (convolutionKernel t x)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let M : α → ℕ := fun a => s a+1
  let k : α → ℕ := fun a => Nat.floor ((M a:ℝ)*x)
  have hsa := mesh_index_atTop hN ht.1 hs
  -- Record the convergence hMa with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hMa : Tendsto M l atTop := by
    exact tendsto_atTop_mono (fun a => Nat.le_succ (s a)) hsa
  -- Record the convergence hMr with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hMr : Tendsto (fun a => (M a:ℝ)/(N a:ℝ)) l (𝓝 t) := by
    have h := hs.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ) |>.comp hN)
    convert h using 1
    · funext a; simp only [M, Nat.cast_add, Nat.cast_one, Function.comp_def]; ring
    · simp
  -- Record the convergence hkm with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hkm : Tendsto (fun a => (k a:ℝ)/(M a:ℝ)) l (𝓝 x) := by
    apply «2606.16671v2».Analysis.floor_mesh_limit hMa tendsto_const_nhds
    exact Eventually.of_forall fun _ => hx.1.le
  -- Record the convergence hkN with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hkN : Tendsto (fun a => (k a:ℝ)/(N a:ℝ)) l (𝓝 (t*x)) := by
    have h := hkm.mul hMr
    convert h using 1
    · funext a
      have hM0 : (M a:ℝ) ≠ 0 := by dsimp [M]; positivity
      field_simp [hM0]
    · ring_nf
  have hqs : ∀ a, k a ≤ s a := by
    intro a
    have hh := «2606.16671v2».Analysis.floor_unit_bounds (M a) (by dsimp [M]; omega) hx
    dsimp [M, k] at hh ⊢
    omega
  -- Record the convergence hqN with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hqN : Tendsto (fun a => ((s a-k a:ℕ):ℝ)/(N a:ℝ)) l (𝓝 (t*(1-x))) := by
    have h := hs.sub hkN
    convert h using 1
    · funext a; rw [Nat.cast_sub (hqs a)]; ring
    · ring_nf
  have ha := ratio_scaled_limit hN
    (show t*x ∈ Ioo (0:ℝ) 1 by
      exact ⟨mul_pos ht.1 hx.1, by nlinarith [ht.1, ht.2, hx.1, hx.2]⟩) hkN
  have hb := ratio_scaled_limit hN
    (show t*(1-x) ∈ Ioo (0:ℝ) 1 by
      exact ⟨mul_pos ht.1 (by linarith [hx.2]), by nlinarith [ht.1, ht.2, hx.1, hx.2]⟩) hqN
  have h := (hMr.mul ha).mul hb
  have hv : t*(1/sqrt (sin (Real.pi*(t*x))))*(1/sqrt (sin (Real.pi*(t*(1-x))))) =
      convolutionKernel t x := by unfold convolutionKernel; ring
  rw [hv] at h
  apply h.congr'
  filter_upwards [hN.eventually_gt_atTop 0] with a hna
  have hNr : 0 < (N a:ℝ) := by exact_mod_cast hna
  change (M a:ℝ)/(N a:ℝ)*(sqrt (N a:ℝ)*ratio (N a) (k a))*
    (sqrt (N a:ℝ)*ratio (N a) (s a-k a)) = _
  have hr2 := sq_sqrt hNr.le
  simp only [convolutionStep, M, k, Nat.cast_add, Nat.cast_one]
  generalize sqrt (N a:ℝ) = r at hr2 ⊢
  field_simp [hNr.ne']
  linear_combination ratio (N a) (Nat.floor (((s a:ℝ)+1)*x))*
    ratio (N a) (s a-Nat.floor (((s a:ℝ)+1)*x))*hr2

/--
The convolution limit includes both singular endpoints, by dominated convergence.

Convergence along the specified source filter to the specified limit: `Tendsto (fun a => ∫ x in
(0:ℝ)..1, convolutionStep (N a) (s a) x) l (𝓝 (convolutionIntegral t))`.

Use: `«2606.16671v2».SineJacobi.endpoint_scaled_limit` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun a => endpoint (N a) (s
a)/sqrt (Real.pi*(N a:ℝ))) l (𝓝 (sineProfile t))`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Use the identities/estimates `«2606.16671v2».Analysis.arcsineBound_integrable`,
`«2606.16671v2».SineJacobi.convolutionStep_measurable`,
`«2606.16671v2».SineJacobi.convolutionStep_bound` with the arguments shown in the proof.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem convolutionIntegral_limit {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {N s : α → ℕ} {t : ℝ} (hN : Tendsto N l atTop) (ht : t ∈ Ioo (0:ℝ) 1)
    (hs : Tendsto (fun a => (s a:ℝ)/(N a:ℝ)) l (𝓝 t)) :
    Tendsto (fun a => ∫ x in (0:ℝ)..1, convolutionStep (N a) (s a) x) l
      (𝓝 (convolutionIntegral t)) := by
  -- Apply the dominated-convergence/Lp transfer after supplying the domination and
  -- pointwise-limit hypotheses.
  let b := (t+1)/2
  have hb : 0 ≤ b := by dsimp [b]; linarith [ht.1]
  have hb1 : b < 1 := by dsimp [b]; linarith [ht.2]
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  let C := (1/sinc (Real.pi*b))^2
  have hdom := «2606.16671v2».Analysis.arcsineBound_integrable.const_mul C
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioo (0:ℝ) 1))
    (bound := fun x => C*«2606.16671v2».Analysis.arcsineBound x)
    (F := fun a x => convolutionStep (N a) (s a) x)
    (f := convolutionKernel t)
    (Eventually.of_forall fun a => (convolutionStep_measurable (N a) (s a)).aestronglyMeasurable)
    (show ∀ᶠ a in l, ∀ᵐ x ∂volume.restrict (Ioo (0:ℝ) 1),
      ‖convolutionStep (N a) (s a) x‖ ≤ C*«2606.16671v2».Analysis.arcsineBound x from by
      filter_upwards [hs.eventually_lt_const htb, hN.eventually_gt_atTop 0] with a ha hna
      have hNr : 0 < (N a:ℝ) := by exact_mod_cast hna
      have hsN : s a < N a := by exact_mod_cast (div_lt_one hNr).mp (ha.trans hb1)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hh := convolutionStep_bound hb hb1 (N a) (s a) hsN ha.le hx
      rw [Real.norm_eq_abs, abs_of_nonneg hh.1]
      exact hh.2)
    hdom
    (show ∀ᵐ x ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun a => convolutionStep (N a) (s a) x) l (𝓝 (convolutionKernel t x)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact convolutionStep_limit hN ht hs hx)
  simpa only [convolutionIntegral, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    restrict_Ioo_eq_restrict_Ioc] using h

end
end «2606.16671v2».SineJacobi
