import chebyshev2.StateRegion.Parametrization

/-!
Article: chebyshev2, Theorem 3.6.
Compact.
Use: `chebyshev2.StateRegion.Scales.normalized_bounds` feeds
`chebyshev2.DualCertificate.Data.normalized_residual_of_admissible` (normalized residual of
admissible).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_analytic` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.StateRegion.Scales
noncomputable section
open Set
variable (S : Scales)
set_option backward.isDefEq.respectTransparency false

/--
Constructs witnesses with the exact properties `∃ t ∈ Icc (0:ℝ) 1, z=(1-t)*lo+t*hi`.

Use: `chebyshev2.StateRegion.Scales.normalized_eq_image` uses this identity to establish
exact identity `S.normalized = S.parametrization '' cube`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `lo=hi` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
theorem interval_mix {lo hi z : ℝ} (h : z ∈ Icc lo hi) :
    ∃ t ∈ Icc (0:ℝ) 1, z=(1-t)*lo+t*hi := by
  -- Separate `lo=hi` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases he : lo=hi
  · refine ⟨0,⟨le_rfl,zero_le_one⟩,?_⟩
    have hz : z=lo := by linarith [h.1,h.2]
    simp [hz]
  · have hp : 0 < hi-lo := by have := h.1.trans h.2; exact sub_pos.mpr (lt_of_le_of_ne this he)
    refine ⟨(z-lo)/(hi-lo),⟨div_nonneg (sub_nonneg.mpr h.1) hp.le,?_⟩,?_⟩
    · exact (div_le_one hp).mpr (by linarith [h.2])
    · field_simp
      ring

/--
Defines `cube` of type `Set (ℝ × ℝ × ℝ)` by `Icc (0:ℝ) 1 ×ˢ (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)`.

Use: `chebyshev2.StateRegion.Scales.parametrization_continuousOn` uses this definition to
establish continuity on the stated domain: `ContinuousOn S.parametrization cube`.

Article: chebyshev2, Proposition 7 via
`chebyshev2.StateRegion.Scales.normalized_compact`.
-/
def cube : Set (ℝ × ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)

/--
Defines `normalized` of type `Set (ℝ × ℝ × ℝ)` by `{p | p.1 ∈ Icc (0:ℝ) 1 ∧ ∃ t ∈ Icc (0:ℝ) 1,
p.2.1=S.V p.1 t ∧ p.2.2 ∈ Icc (S.thetaMinus p.1 t) (S.thetaPlus p.1 t)}`.

Use: `chebyshev2.StateRegion.Scales.states` uses this definition in the displayed
construction of `states`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def normalized : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Icc (0:ℝ) 1 ∧ ∃ t ∈ Icc (0:ℝ) 1,
    p.2.1=S.V p.1 t ∧ p.2.2 ∈ Icc (S.thetaMinus p.1 t) (S.thetaPlus p.1 t)}

/--
Defines `parametrization` of type `ℝ × ℝ × ℝ` by `(p.1,S.V p.1 p.2.1,(1-p.2.2)*S.thetaMinus p.1
p.2.1+p.2.2*S.thetaPlus p.1 p.2.1)`.

Use: `chebyshev2.StateRegion.Scales.normalized_compact` uses this definition to establish
the precise assertion is `IsCompact S.normalized`.

Article: chebyshev2, Proposition 7 via
`chebyshev2.StateRegion.Scales.normalized_compact`.
-/
def parametrization (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.1,S.V p.1 p.2.1,(1-p.2.2)*S.thetaMinus p.1 p.2.1+p.2.2*S.thetaPlus p.1 p.2.1)

/--
Continuity on the stated domain: `ContinuousOn S.parametrization cube`.

Use: `chebyshev2.StateRegion.Scales.normalized_compact` uses this continuity result to
establish the precise assertion is `IsCompact S.normalized`.

Article: chebyshev2, Proposition 7 via
`chebyshev2.StateRegion.Scales.normalized_compact`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.V_continuousOn`,
`chebyshev2.StateRegion.Scales.thetaMinus_continuousOn`,
`chebyshev2.StateRegion.Scales.thetaPlus_continuousOn` with the arguments shown in the
proof.
-/
theorem parametrization_continuousOn : ContinuousOn S.parametrization cube := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.V_continuousOn`,
  -- `chebyshev2.StateRegion.Scales.thetaMinus_continuousOn`,
  -- `chebyshev2.StateRegion.Scales.thetaPlus_continuousOn` with the arguments shown in the
  -- proof.
  have hpair : MapsTo (fun p : ℝ × ℝ × ℝ => (p.1,p.2.1)) cube square :=
    fun _ hp => ⟨hp.1,hp.2.1⟩
  have hV := S.V_continuousOn.comp (by fun_prop) hpair
  have hlo := S.thetaMinus_continuousOn.comp (by fun_prop) hpair
  have hhi := S.thetaPlus_continuousOn.comp (by fun_prop) hpair
  -- Establish continuity hlambda before using the function at limits or in calculus arguments.
  have hlambda : ContinuousOn (fun p : ℝ × ℝ × ℝ => p.2.2) cube := by fun_prop
  exact continuousOn_fst.prodMk (hV.prodMk
    (((continuousOn_const.sub hlambda).mul hlo).add (hlambda.mul hhi)))

/--
Exact identity `S.normalized = S.parametrization '' cube`.

Use: `chebyshev2.StateRegion.Scales.normalized_compact` rewrites with this identity to
establish the precise assertion is `IsCompact S.normalized`.

Article: chebyshev2, Proposition 7 via
`chebyshev2.StateRegion.Scales.normalized_compact`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.interval_mix`,
`chebyshev2.StateRegion.Scales.theta_order` with the arguments shown in the proof.
-/
theorem normalized_eq_image : S.normalized = S.parametrization '' cube := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.interval_mix`,
  -- `chebyshev2.StateRegion.Scales.theta_order` with the arguments shown in the proof.
  ext p
  rcases p with ⟨u,v,z⟩
  constructor
  · intro hp
    obtain ⟨t,ht,hV,hθ⟩ := hp.2
    obtain ⟨l,hl,he⟩ := interval_mix hθ
    dsimp only at hV he
    refine ⟨(u,t,l),⟨hp.1,ht,hl⟩,?_⟩
    change (u,S.V u t,(1-l)*S.thetaMinus u t+l*S.thetaPlus u t)=(u,v,z)
    rw [hV,he]
  · rintro ⟨p,hp,he⟩
    rw [← he]
    rcases p with ⟨u,t,l⟩
    refine ⟨hp.1,t,hp.2.1,rfl,?_⟩
    have hθ := S.theta_order hp.1 hp.2.1
    constructor
    · change S.thetaMinus u t ≤ (1-l)*S.thetaMinus u t+l*S.thetaPlus u t
      nlinarith [mul_nonneg hp.2.2.1 (sub_nonneg.mpr hθ)]
    · change (1-l)*S.thetaMinus u t+l*S.thetaPlus u t ≤ S.thetaPlus u t
      nlinarith [mul_nonneg (sub_nonneg.mpr hp.2.2.2) (sub_nonneg.mpr hθ)]

/--
The precise assertion is `IsCompact S.normalized`.

Use: `chebyshev2.StateRegion.Scales.states_compact` uses this assertion to establish the
precise assertion is `IsCompact S.states`.

Article: chebyshev2, Proposition 7.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.normalized_eq_image`,
`chebyshev2.StateRegion.Scales.parametrization_continuousOn` with the arguments shown in
the proof.
-/
theorem normalized_compact : IsCompact S.normalized := by
  rw [S.normalized_eq_image]
  exact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image_of_continuousOn
    S.parametrization_continuousOn

/--
Defines `stateLift` of type `ℝ × ℝ × ℝ × ℝ` by
`(p.1,p.1*p.2.1/S.k,p.1*p.2.2.1/S.k,p.1*p.2.2.2)`.

Use: `chebyshev2.StateRegion.Scales.states` uses this definition in the displayed
construction of `states`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def stateLift (p : ℝ × (ℝ × ℝ × ℝ)) : ℝ × ℝ × ℝ × ℝ :=
  (p.1,p.1*p.2.1/S.k,p.1*p.2.2.1/S.k,p.1*p.2.2.2)

/--
Defines `states` of type `Set (ℝ × ℝ × ℝ × ℝ)` by `S.stateLift '' (Icc (0:ℝ) 2 ×ˢ
S.normalized)`.

Use: `chebyshev2.StateRegion.Scales.states_compact` uses this definition to establish the
precise assertion is `IsCompact S.states`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def states : Set (ℝ × ℝ × ℝ × ℝ) := S.stateLift '' (Icc (0:ℝ) 2 ×ˢ S.normalized)

/--
The precise assertion is `IsCompact S.states`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.6.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.normalized_compact` with
the arguments shown in the proof.
-/
theorem states_compact : IsCompact S.states :=
  (isCompact_Icc.prod S.normalized_compact).image (by unfold stateLift; fun_prop)

/--
Membership in the specified domain/enclosure: `p.1 ∈ Icc (0:ℝ) 1 ∧ p.2.1 ∈ Icc (0:ℝ) 1 ∧ p.2.2
∈ Icc (0:ℝ) 1`.

Use: `chebyshev2.DualCertificate.Data.normalized_residual_of_admissible` uses this
assertion to prove the quantified assertion `∀ n : ℝ,0≤n →
0≤D.calibration.stateResidual hκ D.ξ₀ D.ξ₁ D.χ D.τ (D.price hκ) (D.statePotential κ)
(PolynomialPotential.unnormalize κ (side.q t,U,V,θ)) n`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.theta_bounds`,
`chebyshev2.StateRegion.Scales.V_bounds`, `chebyshev2.StateRegion.Scales.f_nonneg` with
the arguments shown in the proof.
-/
theorem normalized_bounds {p : ℝ × ℝ × ℝ} (hp : p ∈ S.normalized) :
    p.1 ∈ Icc (0:ℝ) 1 ∧ p.2.1 ∈ Icc (0:ℝ) 1 ∧ p.2.2 ∈ Icc (0:ℝ) 1 := by
  obtain ⟨hu,t,ht,hV,hθ⟩ := hp
  obtain ⟨hlo,hhi⟩ := S.theta_bounds hu ht
  obtain ⟨hfv,hvu⟩ := S.V_bounds hu ht
  refine ⟨hu,?_,⟨hlo.1.trans hθ.1,hθ.2.trans hhi.2⟩⟩
  rw [hV]
  exact ⟨(S.f_nonneg hu).trans hfv,hvu.trans hu.2⟩

end
end chebyshev2.StateRegion.Scales
