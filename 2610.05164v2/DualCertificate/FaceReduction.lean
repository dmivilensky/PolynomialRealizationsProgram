import «2610.05164v2».Residual.CubicConjugate

/-!
Article: 2610.05164v2, Lemma 16.
Convex reduction of the normalized criterion to the two state faces.
Use: `«2610.05164v2».DualCertificate.criterion_le_faces` feeds
`«2610.05164v2».DualCertificate.NormalizedCalibration.actual_face_reduction` (actual face
reduction).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_analytic` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate
noncomputable section
open Set «2610.05164v2».Residual

/--
Defines `criterion` of type `ℝ` by `psi (b-e)-c-e*(1-l)`.

Use: `«2610.05164v2».DualCertificate.criterion_convex` uses this definition to establish the
stated quantitative bound `ConvexOn ℝ univ (fun θ : ℝ => criterion (b₀+b₁*θ) (c₀+c₁*θ) e l)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def criterion (b c e l : ℝ) : ℝ := psi (b-e)-c-e*(1-l)

/--
The stated quantitative bound `ConvexOn ℝ univ (fun θ : ℝ => criterion (b₀+b₁*θ) (c₀+c₁*θ) e
l)`.

Use: `«2610.05164v2».DualCertificate.criterion_le_faces` uses this identity to establish the
stated quantitative bound `criterion (b₀+b₁*θ) (c₀+c₁*θ) e l ≤ max (criterion (b₀+b₁*lo)
(c₀+c₁*lo) e l) (criterion (b₀+b₁*hi) (c₀+c₁*hi) e l)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Residual.psi_convex` with the arguments
shown in the proof.
-/
theorem criterion_convex (b₀ b₁ c₀ c₁ e l : ℝ) :
    ConvexOn ℝ univ (fun θ : ℝ => criterion (b₀+b₁*θ) (c₀+c₁*θ) e l) := by
  -- Use the identities/estimates `«2610.05164v2».Residual.psi_convex` with the arguments shown
  -- in the proof.
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hx : a*(b₀+b₁*x-e)+b*(b₀+b₁*y-e)=b₀+b₁*(a*x+b*y)-e := by
    linear_combination (b₀-e)*hab
  have h := psi_convex.2 (mem_univ _) (mem_univ _) ha hb hab
    (x := b₀+b₁*x-e) (y := b₀+b₁*y-e)
  simp only [smul_eq_mul] at h ⊢
  rw [hx] at h
  unfold criterion
  have hc : a*(c₀+c₁*x)+b*(c₀+c₁*y)=c₀+c₁*(a*x+b*y) := by
    linear_combination c₀*hab
  have he : a*(e*(1-l))+b*(e*(1-l))=e*(1-l) := by
    linear_combination (e*(1-l))*hab
  nlinarith

/--
The stated quantitative bound `criterion (b₀+b₁*θ) (c₀+c₁*θ) e l ≤ max (criterion (b₀+b₁*lo)
(c₀+c₁*lo) e l) (criterion (b₀+b₁*hi) (c₀+c₁*hi) e l)`.

Use: `«2610.05164v2».DualCertificate.criterion_negative_between_faces` uses this bound to
establish the stated quantitative bound `criterion (b₀+b₁*θ) (c₀+c₁*θ) e l < 0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.criterion_convex` with the
arguments shown in the proof.
-/
theorem criterion_le_faces (b₀ b₁ c₀ c₁ e l : ℝ) {θ lo hi : ℝ}
    (hθ : θ ∈ Icc lo hi) :
    criterion (b₀+b₁*θ) (c₀+c₁*θ) e l ≤
      max (criterion (b₀+b₁*lo) (c₀+c₁*lo) e l)
        (criterion (b₀+b₁*hi) (c₀+c₁*hi) e l) :=
  (criterion_convex b₀ b₁ c₀ c₁ e l).le_max_of_mem_Icc
    (mem_univ _) (mem_univ _) hθ
/--
The stated quantitative bound `criterion (b₀+b₁*θ) (c₀+c₁*θ) e l < 0`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 16.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.criterion_le_faces` with
the arguments shown in the proof.
-/
theorem criterion_negative_between_faces (b₀ b₁ c₀ c₁ e l : ℝ) {θ lo hi : ℝ}
    (hθ : θ ∈ Icc lo hi)
    (hlo : criterion (b₀+b₁*lo) (c₀+c₁*lo) e l < 0)
    (hhi : criterion (b₀+b₁*hi) (c₀+c₁*hi) e l < 0) :
    criterion (b₀+b₁*θ) (c₀+c₁*θ) e l < 0 :=
  (criterion_le_faces b₀ b₁ c₀ c₁ e l hθ).trans_lt (max_lt hlo hhi)

end
end «2610.05164v2».DualCertificate
