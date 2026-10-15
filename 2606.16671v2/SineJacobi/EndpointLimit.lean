import «2606.16671v2».SineJacobi.ConvolutionElliptic
import «2606.16671v2».SineJacobi.EndpointBounds
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
Article: 2606.16671v2, Theorem E.3.
The compact-set supremum formulation of E.3 follows from local uniform convergence.
Result: `«2606.16671v2».SineJacobi.endpointProfile_uniformOn` supplies the stated article
conclusion.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Set Filter Topology

/--
Direct endpoint asymptotics with the exact normalization of E.3.

Convergence along the specified source filter to the specified limit: `Tendsto (fun a =>
endpoint (N a) (s a)/sqrt (Real.pi*(N a:ℝ))) l (𝓝 (sineProfile t))`.

Use: `«2606.16671v2».SineJacobi.endpointProfile_locallyUniform` uses this limit to establish
the precise assertion is `TendstoLocallyUniformlyOn endpointProfile sineProfile atTop (Ioo
(0:ℝ) 1)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem endpoint_scaled_limit {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {N s : α → ℕ} {t : ℝ} (hN : Tendsto N l atTop) (ht : t ∈ Ioo (0:ℝ) 1)
    (hs : Tendsto (fun a => (s a:ℝ)/(N a:ℝ)) l (𝓝 t)) :
    Tendsto (fun a => endpoint (N a) (s a)/sqrt (Real.pi*(N a:ℝ))) l
      (𝓝 (sineProfile t)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hconv := convolutionIntegral_limit hN ht hs
  have hr := ratio_scaled_limit hN ht hs
  have hsin : 0 < sin (Real.pi*t) := sin_pos_of_mem_Ioo
    ⟨mul_pos pi_pos ht.1, by nlinarith [pi_pos, ht.2]⟩
  have hh := hconv.div ((tendsto_const_nhds (x := sqrt Real.pi)).mul hr)
    (mul_pos (sqrt_pos.mpr pi_pos) (one_div_pos.mpr (sqrt_pos.mpr hsin))).ne'
  have hv : convolutionIntegral t/(sqrt Real.pi*(1/sqrt (sin (Real.pi*t)))) = sineProfile t := by
    rw [convolutionIntegral_eq_elliptic ht]
    unfold sineProfile
    field_simp [(sqrt_pos.mpr pi_pos).ne', (sqrt_pos.mpr hsin).ne', pi_pos.ne']
  rw [hv] at hh
  apply hh.congr'
  filter_upwards [hN.eventually_gt_atTop 0, hs.eventually_lt_const ht.2] with a hna hsa
  have hNr : 0 < (N a:ℝ) := by exact_mod_cast hna
  have hsN : s a < N a := by exact_mod_cast (div_lt_one hNr).mp hsa
  change (∫ x in (0:ℝ)..1, convolutionStep (N a) (s a) x)/
    (sqrt Real.pi*(sqrt (N a:ℝ)*ratio (N a) (s a))) = _
  rw [convolutionStep_integral, endpoint_convolution (N a) (s a) hsN, sqrt_mul pi_pos.le]
  field_simp [(sqrt_pos.mpr hNr).ne', (sqrt_pos.mpr pi_pos).ne',
    (ratio_pos (N a) (s a) hsN).ne']

/--
Defines `endpointProfile` of type `ℝ` by `endpoint N (Nat.floor ((N:ℝ)*t))/sqrt
(Real.pi*(N:ℝ))`.

Use: `«2606.16671v2».SineJacobi.endpointProfile_locallyUniform` uses this definition to
establish the precise assertion is `TendstoLocallyUniformlyOn endpointProfile sineProfile atTop
(Ioo (0:ℝ) 1)`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpointProfile_uniformOn`.
-/
def endpointProfile (N : ℕ) (t : ℝ) : ℝ :=
  endpoint N (Nat.floor ((N:ℝ)*t))/sqrt (Real.pi*(N:ℝ))

/--
Locally uniform convergence, including the passage from mesh points to arbitrary t.

The precise assertion is `TendstoLocallyUniformlyOn endpointProfile sineProfile atTop (Ioo
(0:ℝ) 1)`.

Use: `«2606.16671v2».SineJacobi.endpointProfile_uniformOn` uses this limit to establish the
precise assertion is `TendstoUniformlyOn endpointProfile sineProfile atTop K`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.endpointProfile_uniformOn`.

Proof: Use the identities/estimates `«2606.16671v2».Analysis.floor_mesh_limit`,
`«2606.16671v2».SineJacobi.endpoint_scaled_limit`,
`«2606.16671v2».SineJacobi.sineProfile_deriv` with the arguments shown in the proof.
-/
theorem endpointProfile_locallyUniform :
    TendstoLocallyUniformlyOn endpointProfile sineProfile atTop (Ioo (0:ℝ) 1) := by
  -- Use the identities/estimates `«2606.16671v2».Analysis.floor_mesh_limit`,
  -- `«2606.16671v2».SineJacobi.endpoint_scaled_limit`,
  -- `«2606.16671v2».SineJacobi.sineProfile_deriv` with the arguments shown in the proof.
  rw [isOpen_Ioo.tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro t ht
  let l : Filter (ℕ × ℝ) := atTop ×ˢ 𝓝 t
  -- Record the convergence hN with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hN : Tendsto (fun a : ℕ × ℝ => a.1) l atTop := tendsto_fst
  -- Record the convergence hx with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hx : Tendsto (fun a : ℕ × ℝ => a.2) l (𝓝 t) := tendsto_snd
  have hfloor := «2606.16671v2».Analysis.floor_mesh_limit hN hx
    (hx.eventually_const_lt ht.1 |>.mono fun _ h => h.le)
  have hp := endpoint_scaled_limit hN ht hfloor
  -- Record the convergence hf with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hf : Tendsto (fun a : ℕ × ℝ => sineProfile a.2) l (𝓝 (sineProfile t)) :=
    (sineProfile_deriv ht).continuousAt.tendsto.comp hx
  apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
  simpa only [dist_self, endpointProfile] using hf.dist hp

/--
The compact-set supremum formulation of E.3 follows from local uniform convergence.

The precise assertion is `TendstoUniformlyOn endpointProfile sineProfile atTop K`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Theorem E.3.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.endpointProfile_locallyUniform`
with the arguments shown in the proof.
-/
theorem endpointProfile_uniformOn {K : Set ℝ} (hK : IsCompact K) (hKi : K ⊆ Ioo (0:ℝ) 1) :
    TendstoUniformlyOn endpointProfile sineProfile atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (endpointProfile_locallyUniform.mono hKi)

end
end «2606.16671v2».SineJacobi
