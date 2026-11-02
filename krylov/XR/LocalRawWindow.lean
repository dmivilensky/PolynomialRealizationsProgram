import krylov.XR.LocalNormalization
import krylov.XR.LocalRelative

/-!
Article: main_krylov, apG:local(a), original unnormalized observed windows.
Use: derive real rank, inverse domains, normalized model coercivity and
the genuine Hermitian gate from original relative secant errors and G2.
No rank-cleanup or gate-success output is supplied as a hypothesis.
Source: exact pair normalization and the proved primitive local estimates.
-/

/-!
Article: krylov, Lemma F.8 [apG:local].

Primitive normalized secant errors and independence derive actual inverse/model/Hermitian
domains, slope and norm bounds, and the true weighted Taylor quotient.
Constants are uniform over p≤n. In a full window the missing direction vanishes and its ℓ,Λ
parameters are unnecessary, as in the corrected G4 and lemma conclusion.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Secant krylov.Convergence
open krylov.Methods hiding unitWindow unitWindow_diagonal_unit unitWindow_norm
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Relative raw secant error is exactly an absolute error after genuine
unit-step normalization, for any true reference operator. -/
theorem unitWindow_reference_error (Q : E →L[ℝ] E) (s y : Fin p → E)
    (hs : ∀ i, s i ≠ 0) (epsilon : ℝ)
    (hy : ∀ i, ‖y i - Q (s i)‖ ≤ epsilon * ‖s i‖) (i : Fin p) :
    ‖unitWindowImages s y i - Q (unitWindow s i)‖ ≤ epsilon := by
  change ‖‖s i‖⁻¹ • y i - Q (‖s i‖⁻¹ • s i)‖ ≤ epsilon
  rw [map_smul, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (hy i) (inv_nonneg.mpr (norm_nonneg _))).trans_eq
    (by field_simp [norm_ne_zero_iff.mpr (hs i)])

/-- The original normalized lower singular-value condition itself forces
rank before cleanup, so rank deletion is not hidden in G2. -/
theorem rawWindow_independent_of_unit_gain (s : Fin p → E) (hs : ∀ i, s i ≠ 0)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hgain : ∀ w : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine (unitWindow s) w‖ ^ 2) :
    LinearIndependent ℝ s := by
  apply Fintype.linearIndependent_iff.mpr
  intro w hw i
  let v := fun j => ‖s j‖ * w j
  have he : combine (unitWindow s) v = 0 := by
    have hid : combine (unitWindow s) v = ∑ j, w j • s j := by
      unfold combine unitWindow rescaleWindow
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [v]
      rw [smul_smul]
      congr 1
      field_simp [norm_ne_zero_iff.mpr (hs j)]
    rw [hid, hw]
  have hb := hgain v
  rw [he, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hb
  have hv : v = 0 := by
    by_contra hne
    have hn : 0 < ‖WithLp.toLp 2 v‖ ^ 2 := sq_pos_of_pos
      (norm_pos_iff.mpr (fun hz => hne ((WithLp.toLp_injective 2) hz)))
    have hp := mul_pos (sq_pos_of_pos hsigma) hn
    linarith
  have hi := congrFun hv i
  change ‖s i‖ * w i = 0 at hi
  exact (mul_eq_zero.mp hi).resolve_left (norm_ne_zero_iff.mpr (hs i))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Real model positivity is invariant under genuine pair normalizers. -/
theorem rescaleModel_posDef_iff (T : Matrix (Fin p) (Fin p) ℝ) (c : Fin p → ℝ)
    (hc : IsUnit (diagonal c).det) : (rescaleModel T c).PosDef ↔ T.PosDef := by
  have hu : IsUnit (diagonal c) := (isUnit_iff_isUnit_det _).mpr hc
  simpa only [rescaleModel, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    diagonal_transpose] using hu.posDef_star_left_conjugate_iff (x := T)

/-- The original physical observed window has both actual inverse domains
and the exact printed normalized c_T coercivity from primitive data only. -/
theorem local_raw_window_domains (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, s i ≠ 0) (mu sigma epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hgain : ∀ w : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine (unitWindow s) w‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon * ‖s i‖)
    (hsmall : (p : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4) :
    LinearIndependent ℝ s ∧ (latest (crossGram s y)).PosDef ∧ IsUnit (crossGram y s).det ∧
      ∀ w : Fin p → ℝ, localCoercivity mu sigma * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        w ⬝ᵥ (latest (crossGram (unitWindow s) (unitWindowImages s y)) *ᵥ w) := by
  have herror := unitWindow_reference_error H s y hs epsilon hy
  have hd := local_observed_domains H hH (unitWindow s) (unitWindowImages s y)
    (unitWindow_norm s hs) mu sigma epsilon hmu hsigma he hpositive hgain herror hsmall
  have hc := unitWindow_diagonal_unit s hs
  have hT : (latest (crossGram s y)).PosDef :=
    (rescaleModel_posDef_iff _ _ hc).mp (by
      have heq : latest (crossGram (unitWindow s) (unitWindowImages s y)) =
          rescaleModel (latest (crossGram s y)) (fun i => ‖s i‖⁻¹) := ss1Model_rescale s y _
      rw [← heq]
      exact hd.1)
  have hA : IsUnit (crossGram y s).det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hdet : (crossGram (unitWindowImages s y) (unitWindow s)).det = 0 := by
      rw [unitWindowImages, unitWindow, window_crossGram_rescale, rescaleModel, det_mul, det_mul, hz,
        mul_zero, zero_mul]
    exact (isUnit_iff_ne_zero.mp hd.2.1) hdet
  exact ⟨rawWindow_independent_of_unit_gain s hs sigma hsigma hgain, hT, hA,
    (local_observed_coercivity H hH (unitWindow s) (unitWindowImages s y)
      (unitWindow_norm s hs) mu sigma epsilon hmu he hpositive hgain herror hsmall).1⟩

/-- The actual original Hermitian test passes under the small primitive
secant budget; it is a conclusion, not an assumption on executed windows. -/
theorem local_raw_windowUnrefuted (theta : ℝ) (htheta : 0 < theta)
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, s i ≠ 0) (mu sigma epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hgain : ∀ w : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine (unitWindow s) w‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon * ‖s i‖)
    (hsmall : (p : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4)
    (hgate : 2 * (p : ℝ) * epsilon / localCoercivity mu sigma < theta) :
    windowUnrefuted theta (crossGram s y) := by
  apply (windowUnrefuted_rescale theta s y _ (unitWindow_diagonal_unit s hs)).mp
  exact local_windowUnrefuted theta htheta H hH (unitWindow s) (unitWindowImages s y)
    (unitWindow_norm s hs) mu sigma epsilon hmu hsigma he hpositive hgain
    (unitWindow_reference_error H s y hs epsilon hy) hsmall hgate

end
end krylov.XR
