import «2606.16671v2».SineJacobi.EndpointBounds
import «2606.16671v2».SineJacobi.Gain
import Mathlib.Algebra.Order.Floor.Semiring

/-!
Article: 2606.16671v2, Theorem E.3.
A uniform dominator independent of both the mesh and the point.
Use: `«2606.16671v2».SineJacobi.greenProfile_uniform_bound` feeds
`«2606.16671v2».SineJacobi.profileProduct_bound` (profile Product bound).
Proof chain: `«2606.16671v2».SineJacobi.greenProfile_eLpNorm_limit` — 2606.16671v2, Theorem E.3;
Hard-edge recurrence, singular ODE, uniqueness and endpoint limits.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Set

/--
The stated quantitative bound `0 < greenWeight N s ∧ greenWeight N s ≤ (9*Real.pi^4/4)*(N:ℝ)`.

Use: `«2606.16671v2».SineJacobi.greenProfile_uniform_bound` uses this bound to establish the
stated quantitative bound `0 ≤ greenProfile N t ∧ greenProfile N t ≤ 9*Real.pi^3/4`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.endpoint_global_bound` with the
arguments shown in the proof.
-/
theorem greenWeight_global_bound (N s : ℕ) (hN : 2 ≤ N) (hs : s < N) :
    0 < greenWeight N s ∧ greenWeight N s ≤ (9*Real.pi^4/4)*(N:ℝ) := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.endpoint_global_bound` with the
  -- arguments shown in the proof.
  have ha := endpoint_global_bound N s hN hs.le
  have hb := endpoint_global_bound N (N-s-1) hN (by omega)
  constructor
  · exact mul_pos ha.1 hb.1
  · have hm := mul_le_mul ha.2 hb.2 hb.1.le
      (show 0 ≤ (3*Real.pi^2/2)*Real.sqrt (N:ℝ) by positivity)
    have he : ((3*Real.pi^2/2)*Real.sqrt (N:ℝ))^2 = (9*Real.pi^4/4)*(N:ℝ) := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
      ring
    simpa only [greenWeight, ← sq, he] using hm

/--
The step function G_N used in E.3, with the paper's πN normalization.

Use: `«2606.16671v2».SineJacobi.greenProfile_uniform_bound` uses this definition to establish
the stated quantitative bound `0 ≤ greenProfile N t ∧ greenProfile N t ≤ 9*Real.pi^3/4`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.
-/
def greenProfile (N : ℕ) (t : ℝ) : ℝ :=
  greenWeight N (Nat.floor ((N:ℝ)*t))/(Real.pi*(N:ℝ))

/--
A uniform dominator independent of both the mesh and the point.

The stated quantitative bound `0 ≤ greenProfile N t ∧ greenProfile N t ≤ 9*Real.pi^3/4`.

Use: `«2606.16671v2».SineJacobi.diagonalProfile_bound` uses this bound to establish the stated
quantitative bound `0 ≤ diagonalProfile N t ∧ diagonalProfile N t ≤ 9*Real.pi^4/4`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.greenWeight_global_bound` with
the arguments shown in the proof.
-/
theorem greenProfile_uniform_bound (N : ℕ) (hN : 2 ≤ N) {t : ℝ} (ht : t ∈ Ico (0:ℝ) 1) :
    0 ≤ greenProfile N t ∧ greenProfile N t ≤ 9*Real.pi^3/4 := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.greenWeight_global_bound` with the
  -- arguments shown in the proof.
  have hpos : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hs : Nat.floor ((N:ℝ)*t) < N := by
    apply (Nat.floor_lt (mul_nonneg hpos.le ht.1)).mpr
    nlinarith [ht.2]
  have hb := greenWeight_global_bound N (Nat.floor ((N:ℝ)*t)) hN hs
  constructor
  · exact div_nonneg hb.1.le (mul_pos pi_pos hpos).le
  · unfold greenProfile
    apply (div_le_iff₀ (mul_pos pi_pos hpos)).mpr
    convert hb.2 using 1 ; ring

end
end «2606.16671v2».SineJacobi
