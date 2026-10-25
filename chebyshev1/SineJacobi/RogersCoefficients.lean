import chebyshev1.SineJacobi.Basic

/-!
Article: chebyshev1, Lemma E.2.
The finite trigonometric identity behind the Rogers coefficient recurrence.
Use: `chebyshev1.SineJacobi.coefficient_terminal_cancel` feeds
`chebyshev1.SineJacobi.rogers_terminal` (At degree N all internal Fourier modes cancel, leaving
the two Chebyshev modes).
Proof chain: `chebyshev1.SineJacobi.terminal` — chebyshev1, Theorem E.1; Sine-lattice
couplings, spectrum, expansion and symmetry.
Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov, q-Ultraspherical
polynomials for q a root of unity — Rogers recurrence and finite Fourier expansion. The needed form
is proved here.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real
open scoped BigOperators

/--
Positive real parts of the finite Rogers q-Pochhammer ratios.

Use: `chebyshev1.SineJacobi.coefficient` uses this definition in the displayed construction
of `coefficient`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.leading_endpoint_max`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.
-/
def ratio (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | k+1 => ratio N k * sin (((k:ℝ)+1/2)*h N) / sin (((k:ℝ)+1)*h N)

/--
Exact identity `ratio N 0 = 1`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev1, Lemma E.2.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem ratio_zero (N : ℕ) : ratio N 0 = 1 := rfl

/--
The stated quantitative bound `0 < ratio N k`.

Use: `chebyshev1.SineJacobi.coefficient_forward` uses this bound to establish exact
identity `coefficient N (s+1) k = coefficient N s k * (sin ((((s-k:ℕ):ℝ)+1/2)*h N) / sin
((((s-k:ℕ):ℝ)+1)*h N)) * (sin (((s:ℝ)+1)*h N) / sin (((s:ℝ)+1/2)*h N))`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.leading_endpoint_max`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Induct on `k`; the recursive step uses the previous-stage assertion.
-/
theorem ratio_pos (N k : ℕ) (hk : k < N) : 0 < ratio N k := by
  -- Induct on `k`; the recursive step uses the previous-stage assertion.
  induction k with
  | zero => norm_num [ratio]
  | succ k ih =>
    rw [ratio]
    have hN : 0 < N := by omega
    have hk' : (k:ℝ)+1 < N := by exact_mod_cast hk
    apply div_pos
    · exact mul_pos (ih (by omega)) (sin_pos_of_mem_Ioo (angle_mem N hN (by positivity) (by linarith)))
    · exact sin_pos_of_mem_Ioo (angle_mem N hN (by positivity) hk')

/--
Defines `coefficient` of type `ℝ` by `if k ≤ s then ratio N k * ratio N (s-k) / ratio N s else
0`.

Use: `chebyshev1.SineJacobi.coefficient_backward` rewrites with this definition to
establish exact identity `coefficient N s (k-1) = coefficient N s k * (sin ((((s-k:ℕ):ℝ)+1/2)*h
N) / sin ((((s-k:ℕ):ℝ)+1)*h N)) * (sin ((k:ℝ)*h N) / sin (((k:ℝ)-1/2)*h N))`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.leading_endpoint_max`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.
-/
def coefficient (N s k : ℕ) : ℝ :=
  if k ≤ s then ratio N k * ratio N (s-k) / ratio N s else 0

/--
The stated quantitative bound `0 < coefficient N s k`.

Use: `chebyshev1.SineJacobi.blockFourier_leading_nonneg` uses this bound to establish the
stated quantitative bound `0 ≤ (blockFourier N 0 s).coeff k`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.leading_endpoint_max`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.ratio_pos` with the arguments
shown in the proof.
-/
theorem coefficient_pos (N s k : ℕ) (hs : s < N) (hk : k ≤ s) :
    0 < coefficient N s k := by
  rw [coefficient, ite_eq_left hk]
  exact div_pos (mul_pos (ratio_pos N k (by omega)) (ratio_pos N (s-k) (by omega))) (ratio_pos N s hs)

/--
Exact identity `coefficient N s 0 = 1`.

Use: `chebyshev1.SineJacobi.rogers_one` rewrites with this identity to establish exact
identity `rogers N 1 = 1+X`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.ratio_pos` with the arguments
shown in the proof.
-/
@[simp] theorem coefficient_zero (N s : ℕ) (hs : s < N) : coefficient N s 0 = 1 := by simp [coefficient, ne_of_gt (ratio_pos N s hs)]

/--
Exact identity `coefficient N s s = 1`.

Use: `chebyshev1.SineJacobi.rogers_one` rewrites with this identity to establish exact
identity `rogers N 1 = 1+X`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.ratio_pos` with the arguments
shown in the proof.
-/
theorem coefficient_last (N s : ℕ) (hs : s < N) : coefficient N s s = 1 := by simp [coefficient, ne_of_gt (ratio_pos N s hs)]

/--
Exact identity `coefficient N s (s-k) = coefficient N s k`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev1, Lemma E.2.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem coefficient_reflect (N s k : ℕ) (hk : k ≤ s) :
    coefficient N s (s-k) = coefficient N s k := by
  simp only [coefficient, ite_eq_left hk, ite_eq_left (Nat.sub_le s k), Nat.sub_sub_self hk]
  rw [mul_comm]

/--
The stated quantitative bound `0 < sin ((k:ℝ)*h N)`.

Use: `chebyshev1.SineJacobi.coefficient_previous` uses this bound to establish exact
identity `4*couplingSq N s * coefficient N (s-1) (k-1) = coefficient N s k * (sin ((s:ℝ)*h
N)*sin ((k:ℝ)*h N) / (sin (((s:ℝ)+1/2)*h N)*sin (((k:ℝ)-1/2)*h N)))`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.angle_mem` with the arguments
shown in the proof.
-/
theorem sin_integer_pos (N k : ℕ) (hk : 0 < k) (hkN : k < N) :
    0 < sin ((k:ℝ)*h N) :=
  sin_pos_of_mem_Ioo (angle_mem N (by omega) (by exact_mod_cast hk) (by exact_mod_cast hkN))

/--
The stated quantitative bound `0 < sin (((k:ℝ)+1/2)*h N)`.

Use: `chebyshev1.SineJacobi.coefficient_previous` uses this bound to establish exact
identity `4*couplingSq N s * coefficient N (s-1) (k-1) = coefficient N s k * (sin ((s:ℝ)*h
N)*sin ((k:ℝ)*h N) / (sin (((s:ℝ)+1/2)*h N)*sin (((k:ℝ)-1/2)*h N)))`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.angle_mem` with the arguments
shown in the proof.
-/
theorem sin_half_pos (N k : ℕ) (hk : k < N) :
    0 < sin (((k:ℝ)+1/2)*h N) := by
  have hk' : (k:ℝ)+1 ≤ N := by exact_mod_cast hk
  exact sin_pos_of_mem_Ioo (angle_mem N (by omega) (by positivity) (by linarith))

/--
Exact identity `ratio N (k-1) = ratio N k * sin ((k:ℝ)*h N) / sin (((k:ℝ)-1/2)*h N)`.

Use: `chebyshev1.SineJacobi.coefficient_backward` rewrites with this identity to establish
exact identity `coefficient N s (k-1) = coefficient N s k * (sin ((((s-k:ℕ):ℝ)+1/2)*h N) / sin
((((s-k:ℕ):ℝ)+1)*h N)) * (sin ((k:ℝ)*h N) / sin (((k:ℝ)-1/2)*h N))`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem ratio_pred (N k : ℕ) (hk : 0 < k) (hkN : k < N) :
    ratio N (k-1) = ratio N k * sin ((k:ℝ)*h N) / sin (((k:ℝ)-1/2)*h N) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp only [Nat.succ_sub_one, ratio, Nat.cast_succ]
  rw [show (j:ℝ)+1-1/2 = (j:ℝ)+1/2 by ring]
  field_simp [ne_of_gt (sin_half_pos N j (by omega)),
    ne_of_gt (sin_integer_pos N (j+1) (by omega) hkN)]
  have ha : sin (((j:ℝ)*2+1)*h N/2) ≠ 0 := by
    convert ne_of_gt (sin_half_pos N j (by omega)) using 1 ; congr 1 ; ring
  have hb : sin (h N*((j:ℝ)+1)) ≠ 0 := by
    convert ne_of_gt (sin_integer_pos N (j+1) (by omega) hkN) using 1
    simp only [Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  field_simp [ha, hb]

/--
Exact identity `coefficient N (s+1) k = coefficient N s k * (sin ((((s-k:ℕ):ℝ)+1/2)*h N) / sin
((((s-k:ℕ):ℝ)+1)*h N)) * (sin (((s:ℝ)+1)*h N) / sin (((s:ℝ)+1/2)*h N))`.

Use: `chebyshev1.SineJacobi.coefficient_recurrence` rewrites with this identity to
establish exact identity `coefficient N (s+1) k = coefficient N s k + coefficient N s (k-1) -
4*couplingSq N s * coefficient N (s-1) (k-1)`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.leading_endpoint_max`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem coefficient_forward (N s k : ℕ) (hs : s+1 < N) (hk : k ≤ s) :
    coefficient N (s+1) k = coefficient N s k *
      (sin ((((s-k:ℕ):ℝ)+1/2)*h N) / sin ((((s-k:ℕ):ℝ)+1)*h N)) *
      (sin (((s:ℝ)+1)*h N) / sin (((s:ℝ)+1/2)*h N)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  simp only [coefficient, ite_eq_left hk, ite_eq_left (show k ≤ s+1 by omega),
    show s+1-k = (s-k)+1 by omega, ratio]
  field_simp [ne_of_gt (ratio_pos N s (by omega)),
    ne_of_gt (sin_integer_pos N (s-k+1) (by omega) (by omega)),
    ne_of_gt (sin_integer_pos N (s+1) (by omega) hs),
    ne_of_gt (sin_half_pos N s (by omega))]

/--
Exact identity `coefficient N s (k-1) = coefficient N s k * (sin ((((s-k:ℕ):ℝ)+1/2)*h N) / sin
((((s-k:ℕ):ℝ)+1)*h N)) * (sin ((k:ℝ)*h N) / sin (((k:ℝ)-1/2)*h N))`.

Use: `chebyshev1.SineJacobi.coefficient_recurrence` rewrites with this identity to
establish exact identity `coefficient N (s+1) k = coefficient N s k + coefficient N s (k-1) -
4*couplingSq N s * coefficient N (s-1) (k-1)`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem coefficient_backward (N s k : ℕ) (hs : s < N) (hk : 0 < k) (hks : k ≤ s) :
    coefficient N s (k-1) = coefficient N s k *
      (sin ((((s-k:ℕ):ℝ)+1/2)*h N) / sin ((((s-k:ℕ):ℝ)+1)*h N)) *
      (sin ((k:ℝ)*h N) / sin (((k:ℝ)-1/2)*h N)) := by
  simp only [coefficient, ite_eq_left hks, ite_eq_left (show k-1 ≤ s by omega),
    show s-(k-1) = (s-k)+1 by omega, ratio]
  rw [ratio_pred N k hk (by omega)]
  field_simp

/--
Exact identity `4*couplingSq N s * coefficient N (s-1) (k-1) = coefficient N s k * (sin
((s:ℝ)*h N)*sin ((k:ℝ)*h N) / (sin (((s:ℝ)+1/2)*h N)*sin (((k:ℝ)-1/2)*h N)))`.

Use: `chebyshev1.SineJacobi.coefficient_recurrence` rewrites with this identity to
establish exact identity `coefficient N (s+1) k = coefficient N s k + coefficient N s (k-1) -
4*couplingSq N s * coefficient N (s-1) (k-1)`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem coefficient_previous (N s k : ℕ) (hs : s < N) (hk : 0 < k) (hks : k ≤ s) :
    4*couplingSq N s * coefficient N (s-1) (k-1) = coefficient N s k *
      (sin ((s:ℝ)*h N)*sin ((k:ℝ)*h N) /
        (sin (((s:ℝ)+1/2)*h N)*sin (((k:ℝ)-1/2)*h N))) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hs0 : 0 < s := by omega
  have hsp : 0 < sin (((s:ℝ)-1/2)*h N) := by
    have hp := sin_half_pos N (s-1) (by omega)
    rw [Nat.cast_sub (by omega : 1 ≤ s)] at hp
    norm_num at hp
    convert hp using 1 ; congr 1 ; ring
  have hkp : 0 < sin (((k:ℝ)-1/2)*h N) := by
    have hp := sin_half_pos N (k-1) (by omega)
    rw [Nat.cast_sub (by omega : 1 ≤ k)] at hp
    norm_num at hp
    convert hp using 1 ; congr 1 ; ring
  simp only [coefficient, ite_eq_left hks, ite_eq_left (show k-1 ≤ s-1 by omega),
    show s-1-(k-1) = s-k by omega]
  rw [ratio_pred N k hk (by omega), ratio_pred N s hs0 hs]
  unfold couplingSq
  field_simp [ne_of_gt (ratio_pos N s hs), ne_of_gt hsp, ne_of_gt hkp,
    ne_of_gt (sin_integer_pos N s hs0 hs), ne_of_gt (sin_half_pos N s hs)]
  ring_nf
  have hsp' : sin (h N*(-1/2)+h N*(s:ℝ)) ≠ 0 := by
    convert ne_of_gt hsp using 1 ; congr 1 ; ring
  field_simp [hsp']
  have hsp'' : sin (h N*(-1+2*(s:ℝ))/2) ≠ 0 := by
    convert ne_of_gt hsp using 1 ; congr 1 ; ring
  field_simp [hsp'']

/--
The finite trigonometric identity behind the Rogers coefficient recurrence.

Exact identity `sin (y-z)*sin (x+y+z)*sin x = sin y*sin (x+y)*sin x + sin (y-z)*sin (x+z)*sin
(x+y) - sin (x+y-z)*sin (x+z)*sin y`.

Use: `chebyshev1.SineJacobi.rogers_ratio_identity` uses this identity to establish the
identity stated in that declaration.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem rogers_sine_identity (x y z : ℝ) :
    sin (y-z)*sin (x+y+z)*sin x =
      sin y*sin (x+y)*sin x + sin (y-z)*sin (x+z)*sin (x+y) -
        sin (x+y-z)*sin (x+z)*sin y := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  simp only [sin_add, sin_sub, cos_add]
  ring_nf
  rw [show cos z^2 = 1-sin z^2 by nlinarith [sin_sq_add_cos_sq z]]
  ring

/--
Exact identity `(sin ((s-k+1/2)*v)/sin ((s-k+1)*v)) * (sin ((s+1)*v)/sin ((s+1/2)*v)) = 1 +
(sin ((s-k+1/2)*v)/sin ((s-k+1)*v)) * (sin (k*v)/sin ((k-1/2)*v)) - sin (s*v)*sin (k*v)/(sin
((s+1/2)*v)*sin ((k-1/2)*v))`.

Use: `chebyshev1.SineJacobi.coefficient_recurrence` uses this identity to establish exact
identity `coefficient N (s+1) k = coefficient N s k + coefficient N s (k-1) - 4*couplingSq N s
* coefficient N (s-1) (k-1)`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem rogers_ratio_identity (s k v : ℝ)
    (h1 : sin ((s-k+1)*v) ≠ 0) (h2 : sin ((s+1/2)*v) ≠ 0)
    (h3 : sin ((k-1/2)*v) ≠ 0) :
    (sin ((s-k+1/2)*v)/sin ((s-k+1)*v)) *
        (sin ((s+1)*v)/sin ((s+1/2)*v)) =
      1 + (sin ((s-k+1/2)*v)/sin ((s-k+1)*v)) *
        (sin (k*v)/sin ((k-1/2)*v)) -
      sin (s*v)*sin (k*v)/(sin ((s+1/2)*v)*sin ((k-1/2)*v)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hi := rogers_sine_identity ((k-1/2)*v) ((s-k+1)*v) (v/2)
  rw [show (s-k+1)*v-v/2 = (s-k+1/2)*v by ring,
    show (k-1/2)*v+(s-k+1)*v+v/2 = (s+1)*v by ring,
    show (k-1/2)*v+(s-k+1)*v = (s+1/2)*v by ring,
    show (k-1/2)*v+v/2 = k*v by ring,
    show (s+1/2)*v-v/2 = s*v by ring] at hi
  have alg (a b c d e f g : ℝ) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
      (hab : a*b*f = d*e*f+a*c*e-g*c*d) :
      a/d*(b/e) = 1+a/d*(c/f)-g*c/(e*f) := by
    field_simp [hd, he, hf]
    linear_combination hab
  exact alg _ _ _ _ _ _ _ h1 h2 h3 hi

/--
Exact identity `coefficient N (s+1) k = coefficient N s k + coefficient N s (k-1) -
4*couplingSq N s * coefficient N (s-1) (k-1)`.

Use: `chebyshev1.SineJacobi.rogers_recurrence` uses this identity to establish exact
identity `rogers N (s+1) = (1+X)*rogers N s - C (4*couplingSq N s)*X*rogers N (s-1)`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.leading_endpoint_max`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sin_half_pos`,
`chebyshev1.SineJacobi.sin_integer_pos`, `chebyshev1.SineJacobi.rogers_ratio_identity`
with the arguments shown in the proof.
-/
theorem coefficient_recurrence (N s k : ℕ) (hs : s+1 < N) (hk : 0 < k) (hks : k ≤ s) :
    coefficient N (s+1) k = coefficient N s k + coefficient N s (k-1) -
      4*couplingSq N s * coefficient N (s-1) (k-1) := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.sin_half_pos`,
  -- `chebyshev1.SineJacobi.sin_integer_pos`,
  -- `chebyshev1.SineJacobi.rogers_ratio_identity` with the arguments shown in the proof.
  have hs0 : 0 < s := by omega
  have hhalf : 0 < sin (((k:ℝ)-1/2)*h N) := by
    have hp := sin_half_pos N (k-1) (by omega)
    rw [Nat.cast_sub (by omega : 1 ≤ k)] at hp
    norm_num at hp
    convert hp using 1 ; congr 1 ; ring
  have hsin : 0 < sin (((s:ℝ)-(k:ℝ)+1)*h N) := by
    convert sin_integer_pos N (s-k+1) (by omega) (by omega) using 1
    rw [Nat.cast_add, Nat.cast_sub hks, Nat.cast_one]
  have hr := rogers_ratio_identity (s:ℝ) (k:ℝ) (h N) (ne_of_gt hsin)
    (ne_of_gt (sin_half_pos N s (by omega))) (ne_of_gt hhalf)
  rw [coefficient_forward N s k hs hks, coefficient_backward N s k (by omega) hk hks,
    coefficient_previous N s k (by omega) hk hks, Nat.cast_sub hks]
  rw [mul_assoc, hr]
  ring

/--
Exact identity `coefficient N (N-1) k + coefficient N (N-1) (k-1) - 4*couplingSq N (N-1) *
coefficient N (N-2) (k-1) = 0`.

Use: `chebyshev1.SineJacobi.rogers_terminal` uses this identity to establish the identity
`(1+X)*rogers N (N-1) - C (4*couplingSq N (N-1))*X*rogers N (N-2) = 1+X^N`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem coefficient_terminal_cancel (N k : ℕ) (hk : 0 < k) (hkN : k < N) :
    coefficient N (N-1) k + coefficient N (N-1) (k-1) -
      4*couplingSq N (N-1) * coefficient N (N-2) (k-1) = 0 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hks : k ≤ N-1 := by omega
  have hhalf : 0 < sin (((k:ℝ)-1/2)*h N) := by
    have hp := sin_half_pos N (k-1) (by omega)
    rw [Nat.cast_sub (by omega : 1 ≤ k)] at hp
    norm_num at hp
    convert hp using 1 ; congr 1 ; ring
  have hsin : 0 < sin ((((N-1:ℕ):ℝ)-(k:ℝ)+1)*h N) := by
    convert sin_integer_pos N ((N-1)-k+1) (by omega) (by omega) using 1
    rw [Nat.cast_add, Nat.cast_sub hks, Nat.cast_one]
  have hr := rogers_ratio_identity ((N-1:ℕ):ℝ) (k:ℝ) (h N) (ne_of_gt hsin)
    (ne_of_gt (sin_half_pos N (N-1) (by omega))) (ne_of_gt hhalf)
  have hz : sin ((((N-1:ℕ):ℝ)+1)*h N) = 0 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
    have he : (N:ℝ)*h N = π := by
      unfold h
      field_simp [show (N:ℝ) ≠ 0 by exact_mod_cast (show N ≠ 0 by omega)]
    rw [he, sin_pi]
  rw [hz, zero_div, mul_zero] at hr
  rw [coefficient_backward N (N-1) k (by omega) hk hks,
    show N-2 = (N-1)-1 by omega, coefficient_previous N (N-1) k (by omega) hk hks,
    Nat.cast_sub hks]
  linear_combination -coefficient N (N-1) k * hr

end
end chebyshev1.SineJacobi
