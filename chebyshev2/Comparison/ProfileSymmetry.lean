import chebyshev2.Comparison.ProfileRepresentation

/-!
Article: chebyshev2, Section 4.1.
Reflection symmetry for arbitrary symmetric comparison profiles.
Use: `chebyshev2.Comparison.Profile.density_reflection` feeds
`chebyshev2.Calibration.ReferenceData.density_reflection` (density reflection).
Proof chain: `chebyshev2.DualCertificate.Data.Admissible` — chebyshev2, Theorem E.1; Stability
of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.PrescribedSpeed chebyshev2.Filters
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {κ : ℝ} (P : chebyshev2.Comparison.Profile κ) (hκ : 0 < κ)
variable (hν : ∀ q ∈ Icc (0:ℝ) 2, P.amplitude (2-q)=P.amplitude q)
include hκ hν

/--
Exact identity `(P.speedData hκ).reciprocal (2-q)=(P.speedData hκ).reciprocal q`.

Use: `chebyshev2.Comparison.Profile.X_reflection` uses this identity to establish exact
identity `(P.speedData hκ).X (2-q)=-(P.speedData hκ).X q`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem reciprocal_reflection (q : ℝ) :
    (P.speedData hκ).reciprocal (2-q)=(P.speedData hκ).reciprocal q := by
  -- Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hq : q ∈ Ioo (0:ℝ) 2
  · have hr : 2-q ∈ Ioo (0:ℝ) 2 := ⟨by linarith [hq.2],by linarith [hq.1]⟩
    simp only [SpeedData.reciprocal,indicator_of_mem hq,indicator_of_mem hr]
    change (P.speed (2-q))⁻¹=(P.speed q)⁻¹
    rw [P.speed_eq ⟨hr.1.le,hr.2.le⟩,P.speed_eq ⟨hq.1.le,hq.2.le⟩,
      hν q ⟨hq.1.le,hq.2.le⟩,chebyshev2.Calibration.Q_reflection]
  · have hr : 2-q ∉ Ioo (0:ℝ) 2 := by
      intro hr
      exact hq ⟨by linarith [hr.2],by linarith [hr.1]⟩
    simp only [SpeedData.reciprocal,indicator_of_notMem hq,indicator_of_notMem hr]

/--
Exact identity `(P.speedData hκ).X (2-q)=-(P.speedData hκ).X q`.

Use: `chebyshev2.Comparison.Profile.coordinate_reflection` rewrites with this identity to
establish exact identity `(P.speedData hκ).q (-x)=2-(P.speedData hκ).q x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.reciprocal_reflection`
with the arguments shown in the proof.
-/
theorem X_reflection (q : ℝ) :
    (P.speedData hκ).X (2-q)=-(P.speedData hκ).X q := by
  -- Use the identities/estimates `chebyshev2.Comparison.Profile.reciprocal_reflection`
  -- with the arguments shown in the proof.
  let S := P.speedData hκ
  have h := intervalIntegral.integral_comp_sub_left (a := 1) (b := q) S.reciprocal 2
  have he : (∫ t in (1:ℝ)..q, S.reciprocal (2-t))=∫ t in (1:ℝ)..q, S.reciprocal t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact P.reciprocal_reflection hκ hν t
  rw [he] at h
  norm_num only at h
  rw [intervalIntegral.integral_symm (a := 1) (b := 2-q)] at h
  change S.X (2-q)=-S.X q
  dsimp only [SpeedData.X]
  linarith

/--
Exact identity `(P.speedData hκ).q (-x)=2-(P.speedData hκ).q x`.

Use: `chebyshev2.Comparison.Profile.density_reflection` rewrites with this identity to
establish exact identity `P.density hκ (-x)=P.density hκ x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.X_reflection`,
`chebyshev2.PrescribedSpeed.SpeedData.q_zero_left`,
`chebyshev2.PrescribedSpeed.SpeedData.q_two_right` with the arguments shown in the proof.
-/
theorem coordinate_reflection (x : ℝ) :
    (P.speedData hκ).q (-x)=2-(P.speedData hκ).q x := by
  -- Use the identities/estimates `chebyshev2.Comparison.Profile.X_reflection`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.q_zero_left`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.q_two_right` with the arguments shown in the
  -- proof.
  let S := P.speedData hκ
  have he : S.X 2=-S.X 0 := by simpa only [sub_zero] using P.X_reflection hκ hν 0
  rcases le_or_gt x (S.X 0) with hl | hl
  · rw [S.q_zero_left hl,S.q_two_right (by linarith)]
    norm_num
  · rcases le_or_gt (S.X 2) x with hr | hr
    · rw [S.q_two_right hr,S.q_zero_left (by linarith)]
      norm_num
    · have hx : x ∈ Icc (S.X 0) (S.X 2) := ⟨hl.le,hr.le⟩
      have hq : 2-S.q x ∈ Icc (0:ℝ) 2 := by
        constructor <;> linarith [(S.q_mem x).1,(S.q_mem x).2]
      have hi := S.q_X hq
      have hX : S.X (2-S.q x)=-x := by
        rw [P.X_reflection hκ hν,S.X_q hx]
      rw [hX] at hi
      exact hi

/--
Exact identity `P.density hκ (-x)=P.density hκ x`.

Use: `chebyshev2.Comparison.Profile.rightFilter_reflection` uses this identity to establish
exact identity `P.rightFilter hκ s q=nonlinear s (P.density hκ) ((P.speedData hκ).X (2-q))`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.density_formula`,
`chebyshev2.Comparison.Profile.coordinate_reflection`,
`chebyshev2.PrescribedSpeed.SpeedData.q_mem` with the arguments shown in the proof.
-/
theorem density_reflection (x : ℝ) : P.density hκ (-x)=P.density hκ x := by
  rw [P.density_formula hκ,P.density_formula hκ,
    P.coordinate_reflection hκ hν,hν _ ((P.speedData hκ).q_mem x)]

/--
Exact identity `P.rightFilter hκ s q=nonlinear s (P.density hκ) ((P.speedData hκ).X (2-q))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem rightFilter_reflection (s q : ℝ) :
    P.rightFilter hκ s q=nonlinear s (P.density hκ) ((P.speedData hκ).X (2-q)) := by
  have hm : reflected (P.density hκ)=P.density hκ := funext (P.density_reflection hκ hν)
  dsimp only [rightFilter]
  rw [hm,P.X_reflection hκ hν]

/--
Exact identity `P.rightLinear hκ q=κ*causal 2 (P.density hκ) ((P.speedData hκ).X (2-q))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem rightLinear_reflection (q : ℝ) :
    P.rightLinear hκ q=κ*causal 2 (P.density hκ) ((P.speedData hκ).X (2-q)) := by
  have hm : reflected (P.density hκ)=P.density hκ := funext (P.density_reflection hκ hν)
  dsimp only [rightLinear]
  rw [hm,P.X_reflection hκ hν]

end
end chebyshev2.Comparison.Profile
