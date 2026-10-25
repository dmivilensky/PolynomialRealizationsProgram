import chebyshev1.SineJacobi.EndpointLimit
import chebyshev1.SineJacobi.ProfileBounds

/-!
Article: chebyshev1, Theorem E.3.
The reflected site carries its exact one-step offset before passing to the limit.
Use: `chebyshev1.SineJacobi.profileProduct_bound` feeds
`chebyshev1.SineJacobi.greenProfile_eLpNorm_limit` (E.3: the actual Green step profiles converge
in every finite Lp, including L2).
Proof chain: `chebyshev1.SineJacobi.greenProfile_eLpNorm_limit` — chebyshev1, Theorem E.3;
Hard-edge recurrence, singular ODE, uniqueness and endpoint limits.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set Filter Topology MeasureTheory

/--
Defines `profileProduct` of type `ℝ` by `sineProfile t*sineProfile (1-t)`.

Use: `chebyshev1.SineJacobi.greenProfile_limit` uses this definition to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
greenProfile N t) atTop (𝓝 (profileProduct t))`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.
-/
def profileProduct (t : ℝ) : ℝ := sineProfile t*sineProfile (1-t)

/--
Continuity on the stated domain: `ContinuousOn profileProduct (Ioo (0:ℝ) 1)`.

Use: `chebyshev1.SineJacobi.profileProduct_aestronglyMeasurable` uses this continuity
result to establish almost-everywhere strong measurability: `AEStronglyMeasurable
profileProduct (volume.restrict (Ioo (0:ℝ) 1))`.

Article: chebyshev1, Theorem 5.1 via
`chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sineProfile_deriv` with the
arguments shown in the proof.
-/
theorem profileProduct_continuousOn : ContinuousOn profileProduct (Ioo (0:ℝ) 1) := by
  intro t ht
  have hr : 1-t ∈ Ioo (0:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  exact ((sineProfile_deriv ht).continuousAt.mul
    ((sineProfile_deriv hr).continuousAt.comp (by fun_prop))).continuousWithinAt

/--
Measurability of the displayed map: `Measurable (greenProfile N)`.

Use: `chebyshev1.SineJacobi.greenProfile_eLpNorm_limit` uses this measurability result to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun N
: ℕ => eLpNorm (fun t => greenProfile N t-profileProduct t) p (volume.restrict (Ioo (0:ℝ) 1)))
atTop (𝓝 0)`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem greenProfile_measurable (N : ℕ) : Measurable (greenProfile N) := by
  unfold greenProfile
  fun_prop

/--
The reflected site carries its exact one-step offset before passing to the limit.

Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
greenProfile N t) atTop (𝓝 (profileProduct t))`.

Use: `chebyshev1.SineJacobi.profileProduct_bound` uses this limit to establish the stated
quantitative bound `0 ≤ profileProduct t ∧ profileProduct t ≤ 9*Real.pi^3/4`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem greenProfile_limit {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    Tendsto (fun N : ℕ => greenProfile N t) atTop (𝓝 (profileProduct t)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let s : ℕ → ℕ := fun N => Nat.floor ((N:ℝ)*t)
  have hs := chebyshev1.Analysis.floor_mesh_limit tendsto_id
    (tendsto_const_nhds (x := t)) (Eventually.of_forall fun _ => ht.1.le)
  change Tendsto (fun N => (s N:ℝ)/(N:ℝ)) atTop (𝓝 t) at hs
  have hsN : ∀ᶠ N : ℕ in atTop, s N < N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
    apply (Nat.floor_lt (mul_pos hNr ht.1).le).mpr
    nlinarith [ht.2]
  -- Record the convergence hq with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hq : Tendsto (fun N => ((N-s N-1:ℕ):ℝ)/(N:ℝ)) atTop (𝓝 (1-t)) := by
    -- Record the convergence hone with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have hone : Tendsto (fun N : ℕ => (N:ℝ)/(N:ℝ)) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop 0] with N hN
      exact (div_self (by exact_mod_cast Nat.ne_of_gt hN)).symm
    have hh := (hone.sub hs).sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [hsN] with N hn
    rw [Nat.cast_sub (by omega : 1 ≤ N-s N), Nat.cast_sub hn.le, Nat.cast_one]
    ring
  have ha := endpoint_scaled_limit tendsto_id ht hs
  have hb := endpoint_scaled_limit tendsto_id
    (show 1-t ∈ Ioo (0:ℝ) 1 from ⟨by linarith [ht.2], by linarith [ht.1]⟩) hq
  have hh := ha.mul hb
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with N hn
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hn
  change (endpoint N (s N)/sqrt (Real.pi*(N:ℝ)))*
    (endpoint N (N-s N-1)/sqrt (Real.pi*(N:ℝ))) = _
  unfold greenProfile greenWeight
  change _ = endpoint N (s N)*endpoint N (N-s N-1)/(Real.pi*(N:ℝ))
  rw [div_mul_div_comm, ← sq, sq_sqrt (mul_pos pi_pos hNr).le]

/--
The stated quantitative bound `0 ≤ profileProduct t ∧ profileProduct t ≤ 9*Real.pi^3/4`.

Use: `chebyshev1.SineJacobi.greenProfile_eLpNorm_limit` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
eLpNorm (fun t => greenProfile N t-profileProduct t) p (volume.restrict (Ioo (0:ℝ) 1))) atTop
(𝓝 0)`.

Article: chebyshev1, Theorem 5.1 via
`chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem profileProduct_bound {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    0 ≤ profileProduct t ∧ profileProduct t ≤ 9*Real.pi^3/4 := by
  have h := greenProfile_limit ht
  have he : ∀ᶠ N : ℕ in atTop, 0 ≤ greenProfile N t ∧ greenProfile N t ≤ 9*Real.pi^3/4 := by
    filter_upwards [eventually_ge_atTop 2] with N hn
    exact greenProfile_uniform_bound N hn ⟨ht.1.le, ht.2⟩
  exact ⟨ge_of_tendsto h (he.mono fun _ hn => hn.1),
    le_of_tendsto h (he.mono fun _ hn => hn.2)⟩

end
end chebyshev1.SineJacobi
