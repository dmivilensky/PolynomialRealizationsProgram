import chebyshev2.GroundState.Coordinate
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: chebyshev2, Proposition 8.
Theorem 3.1, ground-coordinate mass identity.
Use: `chebyshev2.GroundState.RiccatiData.Q_mass` feeds
`chebyshev2.GroundState.GroundWitness.coordinate_mass` (coordinate mass).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.GroundState
noncomputable section
open chebyshev2.Continuum chebyshev2.Sobolev Set MeasureTheory Real Filter
open scoped InnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false

namespace RiccatiData
variable {m : ℝ → ℝ} {c : ℝ} (R : RiccatiData m c)

/--
Exact identity `b=0 ∨ b=2`.

Use: `chebyshev2.GroundState.RiccatiData.q_endpoint_limits` uses this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto R.q atBot (𝓝 0)
∧ Tendsto R.q atTop (𝓝 2)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.coordinate_limits`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem q_limit_roots {l : Filter ℝ} (hμ : ∀ s ∈ l, volume s=⊤)
    (hQ : Integrable R.Q) {b : ℝ} (hb : Tendsto R.q l (𝓝 b)) : b=0 ∨ b=2 := by
  have ht : Tendsto R.Q l (𝓝 (b*(2-b))) := hb.mul (tendsto_const_nhds.sub hb)
  have hz : b*(2-b)=0 := IntegrableAtFilter.eq_zero_of_tendsto
    ⟨univ,univ_mem,by simpa using hQ⟩ hμ ht
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/--
The precise assertion is `¬ Tendsto R.q atTop (𝓝 0)`.

Use: `chebyshev2.GroundState.RiccatiData.q_endpoint_limits` uses this assertion to
establish convergence along the specified source filter to the specified limit: `Tendsto R.q
atBot (𝓝 0) ∧ Tendsto R.q atTop (𝓝 2)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.coordinate_limits`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem q_not_zero_atTop {u : H1} (hpos : ∀ x, 0 < H1.rep u x)
    (hdu : ∀ x, HasDerivAt (H1.rep u) (R.a x*H1.rep u x) x) :
    ¬ Tendsto R.q atTop (𝓝 0) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  intro ht
  have he := ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨b,hb⟩ := eventually_atTop.mp he
  have hmono : MonotoneOn (H1.rep u) (Ici b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici b) (H1.continuous_rep u).continuousOn
      (fun x _ => (hdu x).hasDerivWithinAt)
    intro x hx
    have hx' : b ≤ x := interior_subset hx
    have ha : 0 ≤ R.a x := by have h := hb x hx'; dsimp [q] at h; linarith
    exact mul_nonneg ha (hpos x).le
  have hle : ∀ᶠ x in atTop, H1.rep u b ≤ H1.rep u x :=
    (eventually_ge_atTop b).mono (fun x hx => hmono (show b ∈ Ici b from le_refl b) hx hx)
  have hz : H1.rep u b ≤ 0 := ge_of_tendsto (H1.rep_tendsto_zero u).1 hle
  exact (not_le_of_gt (hpos b)) hz

/--
The precise assertion is `¬ Tendsto R.q atBot (𝓝 2)`.

Use: `chebyshev2.GroundState.RiccatiData.q_endpoint_limits` uses this assertion to
establish convergence along the specified source filter to the specified limit: `Tendsto R.q
atBot (𝓝 0) ∧ Tendsto R.q atTop (𝓝 2)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.coordinate_limits`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem q_not_two_atBot {u : H1} (hpos : ∀ x, 0 < H1.rep u x)
    (hdu : ∀ x, HasDerivAt (H1.rep u) (R.a x*H1.rep u x) x) :
    ¬ Tendsto R.q atBot (𝓝 2) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  intro ht
  have he := ht.eventually (eventually_gt_nhds (by norm_num : (1:ℝ)<2))
  obtain ⟨b,hb⟩ := eventually_atBot.mp he
  have hmono : AntitoneOn (H1.rep u) (Iic b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic b) (H1.continuous_rep u).continuousOn
      (fun x _ => (hdu x).hasDerivWithinAt)
    intro x hx
    have hx' : x ≤ b := show x ∈ Iic b from interior_subset hx
    have ha : R.a x ≤ 0 := by have h := hb x hx'; dsimp [q] at h; linarith
    exact mul_nonpos_of_nonpos_of_nonneg ha (hpos x).le
  have hle : ∀ᶠ x in atBot, H1.rep u b ≤ H1.rep u x :=
    (eventually_le_atBot b).mono (fun x hx => hmono hx (show b ∈ Iic b from le_refl b) hx)
  have hz : H1.rep u b ≤ 0 := ge_of_tendsto (H1.rep_tendsto_zero u).2 hle
  exact (not_le_of_gt (hpos b)) hz

/--
Convergence along the specified source filter to the specified limit: `Tendsto R.q atBot (𝓝 0)
∧ Tendsto R.q atTop (𝓝 2)`.

Use: `chebyshev2.GroundState.RiccatiData.Q_mass` uses this limit to establish exact
identity `(∫ x, R.Q x)=c*(∫ x, m x)-2`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.coordinate_limits`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.q_limits_exist`,
`chebyshev2.GroundState.RiccatiData.q_limit_roots`,
`chebyshev2.GroundState.RiccatiData.Q_integrable` with the arguments shown in the proof.
-/
theorem q_endpoint_limits (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (hc : 0 ≤ c)
    {u : H1} (hpos : ∀ x, 0 < H1.rep u x)
    (hdu : ∀ x, HasDerivAt (H1.rep u) (R.a x*H1.rep u x) x) :
    Tendsto R.q atBot (𝓝 0) ∧ Tendsto R.q atTop (𝓝 2) := by
  -- Use the identities/estimates `chebyshev2.GroundState.RiccatiData.q_limits_exist`,
  -- `chebyshev2.GroundState.RiccatiData.q_limit_roots`,
  -- `chebyshev2.GroundState.RiccatiData.Q_integrable` with the arguments shown in the
  -- proof.
  obtain ⟨lo,hi,hlo,hhi⟩ := R.q_limits_exist hm hn hc
  have hμt : ∀ s ∈ (atTop : Filter ℝ), volume s=⊤ := by
    intro s hs
    obtain ⟨b,hb⟩ := mem_atTop_sets.mp hs
    rw [← top_le_iff,← volume_Ici (a := b)]
    exact measure_mono hb
  have hμb : ∀ s ∈ (atBot : Filter ℝ), volume s=⊤ := by
    intro s hs
    obtain ⟨b,hb⟩ := mem_atBot_sets.mp hs
    apply le_antisymm le_top
    rw [← volume_Iic (a := b)]
    exact measure_mono hb
  have hl : lo=0 := (R.q_limit_roots hμb (R.Q_integrable hm hn hc) hlo).resolve_right
    (fun h => R.q_not_two_atBot hpos hdu (h ▸ hlo))
  have hh : hi=2 := (R.q_limit_roots hμt (R.Q_integrable hm hn hc) hhi).resolve_left
    (fun h => R.q_not_zero_atTop hpos hdu (h ▸ hhi))
  exact ⟨hl ▸ hlo,hh ▸ hhi⟩

/--
Theorem 3.1, ground-coordinate mass identity.

Exact identity `(∫ x, R.Q x)=c*(∫ x, m x)-2`.

Use: `chebyshev2.GroundState.GroundWitness.coordinate_mass` uses this identity to establish
exact identity `(∫ x, G.q x*(2-G.q x))=groundParameter hm hn*(∫ x, m x)-2`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.q_endpoint_limits`,
`chebyshev2.GroundState.RiccatiData.q_derivative_integrable`,
`chebyshev2.Sobolev.locallyAC_integral_eq_sub` with the arguments shown in the proof.
-/
theorem Q_mass (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (hc : 0 ≤ c)
    {u : H1} (hpos : ∀ x, 0 < H1.rep u x)
    (hdu : ∀ x, HasDerivAt (H1.rep u) (R.a x*H1.rep u x) x) :
    (∫ x, R.Q x)=c*(∫ x, m x)-2 := by
  -- Use the identities/estimates `chebyshev2.GroundState.RiccatiData.q_endpoint_limits`,
  -- `chebyshev2.GroundState.RiccatiData.q_derivative_integrable`,
  -- `chebyshev2.Sobolev.locallyAC_integral_eq_sub` with the arguments shown in the proof.
  have hq := R.q_endpoint_limits hm hn hc hpos hdu
  let d : ℝ → ℝ := fun x => c*m x-R.Q x
  -- Establish hd as the integrability justification for the later integral estimates or
  -- changes of order.
  have hd : Integrable d := R.q_derivative_integrable hm hn hc
  have ht : (∫ x in Ioi (0:ℝ), d x)=2-R.q 0 := by
    have he (x : ℝ) : (∫ t in (0:ℝ)..x, d t)=R.q x-R.q 0 :=
      locallyAC_integral_eq_sub R.q_locallyAC R.q_derivative_ae 0 x
    exact tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hd.integrableOn tendsto_id)
      (by simpa only [id_eq,he] using hq.2.sub_const (R.q 0))
  have hb : (∫ x in Iic (0:ℝ), d x)=R.q 0 := by
    have he (x : ℝ) : (∫ t in x..(0:ℝ), d t)=R.q 0-R.q x :=
      locallyAC_integral_eq_sub R.q_locallyAC R.q_derivative_ae x 0
    exact tendsto_nhds_unique (intervalIntegral_tendsto_integral_Iic 0 hd.integrableOn tendsto_id)
      (by simpa only [id_eq,he,sub_zero] using hq.1.const_sub (R.q 0))
  have hmass : (∫ x, d x)=2 := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hd.integrableOn hd.integrableOn (b := 0),ht,hb]
    ring
  change (∫ x, c*m x-R.Q x)=2 at hmass
  rw [integral_sub (hm.const_mul c) (R.Q_integrable hm hn hc),integral_const_mul] at hmass
  linarith

end RiccatiData
end
end chebyshev2.GroundState
