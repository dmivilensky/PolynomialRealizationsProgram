import chebyshev1.TwoTerm.Basic

/-!
Article: chebyshev1, Theorem C.1.
Theorem C.1, for every used noninitial time.
Result: `chebyshev1.TwoTerm.coefficients_unique_explicit` supplies the stated article
conclusion.
-/
namespace chebyshev1
noncomputable section
open Polynomial
open scoped Polynomial

/--
Triangular coefficient comparison for degrees n+2, n+1, n.

Exact identity `a = 0 ∧ g = 0 ∧ b = 0`.

Use: `chebyshev1.TwoTerm.local_unique` uses this identity to establish the identity `a =
1 + Prefix.beta I (n + 1) ∧ b = -Prefix.beta I (n + 1) ∧ g = Prefix.gamma I (n + 1)`.

Article: chebyshev1, Theorem C.1 via `chebyshev1.TwoTerm.local_unique`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem affine_polynomial_independence {p q : ℝ[X]} {n : ℕ}
    (hp : p.natDegree = n + 1) (hq : q.natDegree = n) (hq0 : q ≠ 0)
    {a g b : ℝ} (h : (C a - C g * X) * p + C b * q = 0) :
    a = 0 ∧ g = 0 ∧ b = 0 := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hp0 : p ≠ 0 := by
    intro he
    rw [he, natDegree_zero] at hp
    omega
  have hlead : p.coeff (n + 1) ≠ 0 := by
    rw [← hp, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp0
  have hp2 : p.coeff (n + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hq2 : q.coeff (n + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hq1 : q.coeff (n + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have he : C a * p - C g * (X * p) + C b * q = 0 := by
    linear_combination h
  have hg := congrArg (fun f : ℝ[X] => f.coeff (n + 2)) he
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, hp2, hq2, coeff_zero,
    mul_zero, zero_sub] at hg
  have hg0 : g = 0 := by
    have hh : g * p.coeff (n + 1) = 0 := by linarith
    exact (mul_eq_zero.mp hh).resolve_right hlead
  have ha := congrArg (fun f : ℝ[X] => f.coeff (n + 1)) he
  simp only [coeff_add, coeff_sub, coeff_C_mul, hg0, zero_mul, sub_zero, hq1,
    mul_zero, add_zero, coeff_zero] at ha
  have ha0 : a = 0 := (mul_eq_zero.mp ha).resolve_right hlead
  have hb : C b * q = 0 := by simpa [ha0, hg0] using h
  have hb0 : b = 0 := C_eq_zero.mp ((mul_eq_zero.mp hb).resolve_right hq0)
  exact ⟨ha0, hg0, hb0⟩

namespace TwoTerm

/--
Local coefficient uniqueness (C.1), requiring only the three scalar prefixes.

Exact identity `a = 1 + Prefix.beta I (n + 1) ∧ b = -Prefix.beta I (n + 1) ∧ g = Prefix.gamma I
(n + 1)`.

Use: `chebyshev1.TwoTerm.coefficients_unique` uses this identity to establish exact
identity `S.a t = 1 + Prefix.beta I t ∧ S.b t = -Prefix.beta I t ∧ S.gamma t = Prefix.gamma I
t`.

Article: chebyshev1, Theorem C.1.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.polynomial_eq`,
`chebyshev1.Prefix.residual_recurrence`, `chebyshev1.Prefix.gamma_succ` with the
arguments shown in the proof.
-/
theorem local_unique (I : SpectralInterval) (n : ℕ) (a b g : ℝ)
    (h : ∀ lam ∈ Set.Icc I.mu I.L,
      (I.residual (n + 2)).eval lam =
        (a - g * lam) * (I.residual (n + 1)).eval lam + b * (I.residual n).eval lam) :
    a = 1 + Prefix.beta I (n + 1) ∧ b = -Prefix.beta I (n + 1) ∧
      g = Prefix.gamma I (n + 1) := by
  -- Use the identities/estimates `chebyshev1.SpectralInterval.polynomial_eq`,
  -- `chebyshev1.Prefix.residual_recurrence`, `chebyshev1.Prefix.gamma_succ` with the
  -- arguments shown in the proof.
  have hpoly : I.residual (n + 2) =
      (C a - C g * X) * I.residual (n + 1) + C b * I.residual n := by
    apply I.polynomial_eq
    simpa using h
  have hstd : I.residual (n + 2) =
      (C (1 + Prefix.beta I (n + 1)) - C (Prefix.gamma I (n + 1)) * X) *
        I.residual (n + 1) + C (-Prefix.beta I (n + 1)) * I.residual n := by
    rw [Prefix.residual_recurrence, Prefix.gamma_succ, map_mul, map_neg]
    ring
  have hdiff :
      (C (a - (1 + Prefix.beta I (n + 1))) - C (g - Prefix.gamma I (n + 1)) * X) *
        I.residual (n + 1) + C (b + Prefix.beta I (n + 1)) * I.residual n = 0 := by
    simp only [map_sub, map_add]
    linear_combination (norm := (simp only [map_add, map_neg, map_one]; ring_nf)) hstd - hpoly
  obtain ⟨ha, hg, hb⟩ := affine_polynomial_independence
    (I.residual_natDegree (n + 1)) (I.residual_natDegree n) (I.residual_ne_zero n) hdiff
  exact ⟨by linarith, by linarith, by linarith⟩

/--
Exact identity `S.gamma 0 = 2 / (I.L + I.mu)`.

Use: `chebyshev1.TwoTerm.gamma_eq_prefix` uses this identity to establish the identity
`S.gamma s = Prefix.gamma I s`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.

Proof: Use the identities/estimates `chebyshev1.Prefix.residual_one`,
`chebyshev1.TwoTerm.transfer_one` with the arguments shown in the proof.
-/
theorem initial_unique (S : TwoTerm) (I : SpectralInterval) (N : ℕ) (hN : 1 ≤ N)
    (h : S.PrefixExact I N) : S.gamma 0 = 2 / (I.L + I.mu) := by
  have he := h 1 hN I.mu ⟨le_rfl, I.mu_lt_L.le⟩
  rw [transfer_one, Prefix.residual_one] at he
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X] at he
  nlinarith [I.mu_pos]

/--
Theorem C.1, for every used noninitial time.

Exact identity `S.a t = 1 + Prefix.beta I t ∧ S.b t = -Prefix.beta I t ∧ S.gamma t =
Prefix.gamma I t`.

Use: `chebyshev1.TwoTerm.coefficients_unique_explicit` uses this identity to establish
exact identity `S.a t = 1 + Prefix.beta I t ∧ S.b t = -Prefix.beta I t ∧ S.gamma t = (1 +
Prefix.beta I t) * (2 / (I.L + I.mu))`.

Article: chebyshev1, Theorem C.1 via `chebyshev1.TwoTerm.coefficients_unique_explicit`.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.local_unique`,
`chebyshev1.TwoTerm.transfer_recurrence` with the arguments shown in the proof.
-/
theorem coefficients_unique (S : TwoTerm) (I : SpectralInterval) (N t : ℕ)
    (ht : 1 ≤ t) (htN : t < N) (h : S.PrefixExact I N) :
    S.a t = 1 + Prefix.beta I t ∧ S.b t = -Prefix.beta I t ∧ S.gamma t = Prefix.gamma I t := by
  -- Use the identities/estimates `chebyshev1.TwoTerm.local_unique`,
  -- `chebyshev1.TwoTerm.transfer_recurrence` with the arguments shown in the proof.
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  apply local_unique
  intro lam hl
  rw [← h (n + 2) (by omega) lam hl, transfer_recurrence,
    h (n + 1) (by omega) lam hl, h n (by omega) lam hl]

/--
Exact identity `S.a t = 1 + Prefix.beta I t ∧ S.b t = -Prefix.beta I t ∧ S.gamma t = (1 +
Prefix.beta I t) * (2 / (I.L + I.mu))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem C.1.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.coefficients_unique`,
`chebyshev1.Prefix.gamma_succ` with the arguments shown in the proof.
-/
theorem coefficients_unique_explicit (S : TwoTerm) (I : SpectralInterval) (N t : ℕ)
    (ht : 1 ≤ t) (htN : t < N) (h : S.PrefixExact I N) :
    S.a t = 1 + Prefix.beta I t ∧ S.b t = -Prefix.beta I t ∧
      S.gamma t = (1 + Prefix.beta I t) * (2 / (I.L + I.mu)) := by
  obtain ⟨ha, hb, hg⟩ := coefficients_unique S I N t ht htN h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  exact ⟨ha, hb, hg.trans (Prefix.gamma_succ I n)⟩

end TwoTerm
end
end chebyshev1
