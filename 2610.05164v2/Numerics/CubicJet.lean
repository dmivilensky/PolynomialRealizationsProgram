import «2610.05164v2».Numerics.JetRules
import «2610.05164v2».Numerics.CubicRoot
import «2610.05164v2».DualCertificate.CubicSmooth

/-!
Article: 2610.05164v2, Lemma 19.
Positive-cubic smoothness and triangular jet recurrence.
Use: `«2610.05164v2».Numerics.positiveCubic_jet_recurrence` feeds
`«2610.05164v2».Numerics.cubicJetCheck_encloses` (cubic Jet Check encloses).
-/
namespace «2610.05164v2».Numerics
noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Smoothness to the stated order: `ContDiffOn ℝ n (fun t => positiveCubic (a t) (b t)) s`.

Use: `«2610.05164v2».Numerics.positiveCubic_jet_recurrence` uses this identity to establish the
precise assertion is `let z`.

Article: 2610.05164v2, Lemma 19.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.positiveRoot_contDiffOn` with
the arguments shown in the proof.
-/
theorem positiveCubic_smooth {a b : ℝ → ℝ} {s : Set ℝ} {n : ℕ∞}
    (ha : ContDiffOn ℝ n a s) (hb : ContDiffOn ℝ n b s)
    (ha0 : ∀ t∈s,0≤a t) (hb0 : ∀ t∈s,0<b t) :
    ContDiffOn ℝ n (fun t => positiveCubic (a t) (b t)) s := by
  apply («2610.05164v2».Calibration.positiveRoot_contDiffOn.of_le (by simp)).comp
    (contDiffOn_const.prodMk ((ha.div_const 3).prodMk hb))
  intro t ht
  exact ⟨by norm_num,div_nonneg (ha0 t ht) (by norm_num),hb0 t ht⟩

/--
Exact identity `3*(positiveCubic a b)^2-a=2*a+3*b/positiveCubic a b ∧ 0<2*a+3*b/positiveCubic a
b`.

Use: `«2610.05164v2».Numerics.positiveCubic_jet_recurrence` uses this identity to establish the
precise assertion is `let z`.

Article: 2610.05164v2, Lemma 19.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem positiveCubic_slope {a b : ℝ} (ha : 0≤a) (hb : 0<b) :
    3*(positiveCubic a b)^2-a=2*a+3*b/positiveCubic a b ∧
      0<2*a+3*b/positiveCubic a b := by
  obtain ⟨hz,he⟩ := positiveCubic_spec ha hb
  constructor
  · field_simp
    nlinarith [he]
  · positivity

/--
The stated quantitative bound `(3*z x^2-a x)*normalizedWithin z s (n+1) x= normalizedWithin b s
(n+1) x+ (∑ i∈Finset.range (n+1),normalizedWithin a s (i+1) x*normalizedWithin z s (n-i) x)-
3*z x*normalizedWithin (fun t => (z t-z x)^2) s (n+1) x- normalizedWithin (fun t => (z t-z
x)^3) s (n+1) x`.

Use: `«2610.05164v2».Numerics.positiveCubic_jet_recurrence` uses this identity to establish the
precise assertion is `let z`.

Article: 2610.05164v2, Lemma 19 via `«2610.05164v2».Numerics.positiveCubic_jet_recurrence`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.normalizedWithin_congr`,
`«2610.05164v2».Numerics.normalizedWithin_add`,
`«2610.05164v2».Numerics.normalizedWithin_const` with the arguments shown in the proof.
-/
theorem normalizedWithin_cubic {a b z : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (ha : ContDiffWithinAt ℝ (n+1) a s x) (hb : ContDiffWithinAt ℝ (n+1) b s x)
    (hz : ContDiffWithinAt ℝ (n+1) z s x)
    (heq : ∀ t∈s,z t^3=a t*z t+b t) :
    (3*z x^2-a x)*normalizedWithin z s (n+1) x=
      normalizedWithin b s (n+1) x+
      (∑ i∈Finset.range (n+1),normalizedWithin a s (i+1) x*normalizedWithin z s (n-i) x)-
      3*z x*normalizedWithin (fun t => (z t-z x)^2) s (n+1) x-
      normalizedWithin (fun t => (z t-z x)^3) s (n+1) x := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.normalizedWithin_congr`,
  -- `«2610.05164v2».Numerics.normalizedWithin_add`,
  -- `«2610.05164v2».Numerics.normalizedWithin_const` with the arguments shown in the proof.
  let u := fun t => z t-z x
  have hu : ContDiffWithinAt ℝ (n+1) u s x := hz.sub contDiffWithinAt_const
  have hc : normalizedWithin (fun t => z t^3) s (n+1) x=
      3*z x^2*normalizedWithin z s (n+1) x+
      3*z x*normalizedWithin (fun t => u t^2) s (n+1) x+
      normalizedWithin (fun t => u t^3) s (n+1) x := by
    rw [normalizedWithin_congr (g := fun t => z x^3+
      (3*z x^2*u t+3*z x*u t^2+u t^3)) (fun t _ => by dsimp [u];ring) (n+1) hx]
    rw [normalizedWithin_add hs hx contDiffWithinAt_const
      (((contDiffWithinAt_const.mul hu).add (contDiffWithinAt_const.mul (hu.pow 2))).add (hu.pow 3)),
      normalizedWithin_const (j := n+1) (by omega),zero_add,
      normalizedWithin_add hs hx ((contDiffWithinAt_const.mul hu).add
        (contDiffWithinAt_const.mul (hu.pow 2))) (hu.pow 3),
      normalizedWithin_add hs hx (contDiffWithinAt_const.mul hu)
        (contDiffWithinAt_const.mul (hu.pow 2)),
      normalizedWithin_const_mul,normalizedWithin_const_mul,
      normalizedWithin_sub_const (j := n+1) (by omega)]
  have hab : normalizedWithin (fun t => z t^3) s (n+1) x=
      normalizedWithin (fun t => a t*z t+b t) s (n+1) x :=
    normalizedWithin_congr heq (n+1) hx
  rw [normalizedWithin_add hs hx (ha.mul hz) hb,
    normalizedWithin_mul hs hx ha hz,Finset.sum_range_succ',normalizedWithin_zero] at hab
  simp only [Nat.sub_zero,show ∀ i : ℕ,n+1-(i+1)=n-i by omega] at hab
  rw [hc] at hab
  dsimp only [u] at hab
  linarith

/--
The stated quantitative bound `normalizedWithin (fun t => (z t-z x)^2) s (n+1) x= ∑
i∈Finset.range n,normalizedWithin z s (i+1) x*normalizedWithin z s (n-i) x`.

Use: `«2610.05164v2».Numerics.normalizedWithin_centered_cube` uses this identity to establish
the identity stated in that declaration.

Article: 2610.05164v2, Lemma 19 via `«2610.05164v2».Numerics.positiveCubic_jet_recurrence`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem normalizedWithin_centered_square {z : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s) (hz : ContDiffWithinAt ℝ (n+1) z s x) :
    normalizedWithin (fun t => (z t-z x)^2) s (n+1) x=
      ∑ i∈Finset.range n,normalizedWithin z s (i+1) x*normalizedWithin z s (n-i) x := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hu := hz.sub (contDiffWithinAt_const (c := z x))
  rw [show (fun t => (z t-z x)^2)=(fun t => (z t-z x)*(z t-z x)) by funext t;ring,
    normalizedWithin_mul_vanishing hs hx hu hu (sub_self _) (sub_self _)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [normalizedWithin_sub_const (by omega),normalizedWithin_sub_const (by omega)]

/--
The stated quantitative bound `normalizedWithin (fun t => (z t-z x)^3) s (n+1) x= ∑
i∈Finset.range n,normalizedWithin z s (i+1) x* ∑ j∈Finset.range (n-i-1),normalizedWithin z s
(j+1) x*normalizedWithin z s (n-i-1-j) x`.

Use: `«2610.05164v2».Numerics.positiveCubic_jet_recurrence` rewrites with this identity to
establish the precise assertion is `let z`.

Article: 2610.05164v2, Lemma 19 via `«2610.05164v2».Numerics.positiveCubic_jet_recurrence`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem normalizedWithin_centered_cube {z : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s) (hz : ContDiffWithinAt ℝ (n+1) z s x) :
    normalizedWithin (fun t => (z t-z x)^3) s (n+1) x=
      ∑ i∈Finset.range n,normalizedWithin z s (i+1) x*
        ∑ j∈Finset.range (n-i-1),normalizedWithin z s (j+1) x*normalizedWithin z s (n-i-1-j) x := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hu := hz.sub (contDiffWithinAt_const (c := z x))
  rw [show (fun t => (z t-z x)^3)=(fun t => (z t-z x)*(z t-z x)^2) by funext t;ring,
    normalizedWithin_mul_vanishing hs hx hu (hu.pow 2) (sub_self _) (by simp)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [normalizedWithin_sub_const (by omega)]
  have hn : n-i=(n-i-1)+1 := by omega
  have he := normalizedWithin_centered_square (n := n-i-1) hs hx
    (hz.of_le (by exact_mod_cast (show n-i-1+1≤n+1 by omega)))
  rw [← hn] at he
  rw [he]

/--
Lemma 18's fully triangular cubic recurrence. Every jet on the right has order at most n; the
denominator is strictly positive.

The precise assertion is `let z`.

Use: `«2610.05164v2».Numerics.cubicJetCheck_encloses` rewrites with this assertion to establish
the stated quantitative bound `JetEncloses Z (fun t => positiveCubic (a t) (b t)) s x N`.

Article: 2610.05164v2, Lemma 19.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.positiveCubic_smooth`,
`«2610.05164v2».Numerics.normalizedWithin_cubic`, `«2610.05164v2».Numerics.positiveCubic_spec`
with the arguments shown in the proof.
-/
theorem positiveCubic_jet_recurrence {a b : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (ha : ContDiffOn ℝ (n+1) a s) (hb : ContDiffOn ℝ (n+1) b s)
    (ha0 : ∀ t∈s,0≤a t) (hb0 : ∀ t∈s,0<b t) :
    let z := fun t => positiveCubic (a t) (b t)
    normalizedWithin z s (n+1) x=
      (normalizedWithin b s (n+1) x+
        (∑ i∈Finset.range (n+1),normalizedWithin a s (i+1) x*normalizedWithin z s (n-i) x)-
        3*z x*(∑ i∈Finset.range n,normalizedWithin z s (i+1) x*normalizedWithin z s (n-i) x)-
        (∑ i∈Finset.range n,normalizedWithin z s (i+1) x*
          ∑ j∈Finset.range (n-i-1),normalizedWithin z s (j+1) x*normalizedWithin z s (n-i-1-j) x))/
      (2*a x+3*b x/z x) := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.positiveCubic_smooth`,
  -- `«2610.05164v2».Numerics.normalizedWithin_cubic`,
  -- `«2610.05164v2».Numerics.positiveCubic_spec` with the arguments shown in the proof.
  dsimp only
  let z := fun t => positiveCubic (a t) (b t)
  have hz := positiveCubic_smooth ha hb ha0 hb0
  have he := normalizedWithin_cubic (z := z) hs hx (ha x hx) (hb x hx) (hz x hx)
    (fun t ht => by dsimp [z];linarith [(positiveCubic_spec (ha0 t ht) (hb0 t ht)).2])
  rw [normalizedWithin_centered_square hs hx (hz x hx),
    normalizedWithin_centered_cube hs hx (hz x hx)] at he
  have hd := positiveCubic_slope (ha0 x hx) (hb0 x hx)
  rw [hd.1] at he
  exact (eq_div_iff (ne_of_gt hd.2)).mpr (by simpa only [mul_comm] using he)

end
end «2610.05164v2».Numerics
