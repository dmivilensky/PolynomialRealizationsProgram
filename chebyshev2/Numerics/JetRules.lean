import chebyshev2.Numerics.Quadrature
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
Article: chebyshev2, Lemma 18.
Normalized derivative arithmetic on sets with unique derivatives.
Use: `chebyshev2.Numerics.normalizedWithin_shifted_riccati` feeds
`chebyshev2.Numerics.riccatiJetCheck_sound` (riccati Jet Check sound).
Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative recurrences. The
needed form is proved here.
-/
namespace chebyshev2.Numerics
noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Defines `normalizedWithin` of type `ℝ` by `iteratedDerivWithin j f s x/(j.factorial:ℝ)`.

Use: `chebyshev2.Numerics.normalizedWithin_add` rewrites with this definition to establish
the stated quantitative bound `normalizedWithin (fun t => f t+g t) s j x= normalizedWithin f s
j x+normalizedWithin g s j x`.

Article: chebyshev2, Lemma 18 via `chebyshev2.Numerics.normalizedWithin_exp`.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.
-/
def normalizedWithin (f : ℝ → ℝ) (s : Set ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  iteratedDerivWithin j f s x/(j.factorial:ℝ)

/--
Exact identity `normalizedWithin f s 0 x=f x`.

Use: `chebyshev2.Numerics.normalizedWithin_inverse` rewrites with this identity to
establish the stated quantitative bound `normalizedWithin (fun t => (f t)⁻¹) s j x= -(∑
i∈Finset.range j,normalizedWithin f s (i+1) x* normalizedWithin (fun t => (f t)⁻¹) s (j-(i+1))
x)/f x`.

Article: chebyshev2, Lemma 18 via `chebyshev2.Numerics.normalizedWithin_inverse`.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem normalizedWithin_zero (f : ℝ → ℝ) (s : Set ℝ) (x : ℝ) :
    normalizedWithin f s 0 x=f x := by simp [normalizedWithin]

/--
Exact identity `normalizedWithin f univ j x=normalizedDerivative f j x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 18.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedWithin_univ (f : ℝ → ℝ) (j : ℕ) (x : ℝ) :
    normalizedWithin f univ j x=normalizedDerivative f j x := by simp [normalizedWithin,normalizedDerivative]

/--
Exact identity `normalizedWithin f s j x=normalizedWithin g s j x`.

Use: `chebyshev2.Numerics.normalizedWithin_exp` rewrites with this identity to establish
the stated quantitative bound `(j+1)*normalizedWithin (fun t => Real.exp (f t)) s (j+1) x= ∑
i∈Finset.range (j+1),(i+1)*normalizedWithin f s (i+1) x* normalizedWithin (fun t => Real.exp (f
t)) s (j-i) x`.

Article: chebyshev2, Lemma 18 via `chebyshev2.Numerics.normalizedWithin_exp`.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedWithin_congr {f g : ℝ → ℝ} {s : Set ℝ} (he : EqOn f g s)
    (j : ℕ) {x : ℝ} (hx : x∈s) : normalizedWithin f s j x=normalizedWithin g s j x := by rw [normalizedWithin,normalizedWithin,iteratedDerivWithin_congr he hx]

/--
The stated quantitative bound `normalizedWithin (fun t => f t+g t) s j x= normalizedWithin f s
j x+normalizedWithin g s j x`.

Use: `chebyshev2.Numerics.normalizedWithin_riccati` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Lemma 18 via `chebyshev2.Numerics.normalizedWithin_riccati`.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedWithin_add {f g : ℝ → ℝ} {s : Set ℝ} {j : ℕ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (hf : ContDiffWithinAt ℝ j f s x) (hg : ContDiffWithinAt ℝ j g s x) :
    normalizedWithin (fun t => f t+g t) s j x=
      normalizedWithin f s j x+normalizedWithin g s j x := by simp only [normalizedWithin,iteratedDerivWithin_fun_add hx hs hf hg,add_div]

/--
The stated quantitative bound `normalizedWithin (fun t => f t*g t) s j x= ∑ i∈Finset.range
(j+1),normalizedWithin f s i x*normalizedWithin g s (j-i) x`.

Use: `chebyshev2.Numerics.normalizedWithin_exp` rewrites with this identity to establish
the stated quantitative bound `(j+1)*normalizedWithin (fun t => Real.exp (f t)) s (j+1) x= ∑
i∈Finset.range (j+1),(i+1)*normalizedWithin f s (i+1) x* normalizedWithin (fun t => Real.exp (f
t)) s (j-i) x`.

Article: chebyshev2, Lemma 18.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem normalizedWithin_mul {f g : ℝ → ℝ} {s : Set ℝ} {j : ℕ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (hf : ContDiffWithinAt ℝ j f s x) (hg : ContDiffWithinAt ℝ j g s x) :
    normalizedWithin (fun t => f t*g t) s j x=
      ∑ i∈Finset.range (j+1),normalizedWithin f s i x*normalizedWithin g s (j-i) x := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  change iteratedDerivWithin j (f*g) s x/(j.factorial:ℝ)=_
  rw [iteratedDerivWithin_mul hx hs hf hg,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i≤j := by have := Finset.mem_range.mp hi;omega
  have hfac : (j.choose i:ℝ)*(i.factorial:ℝ)*((j-i).factorial:ℝ)=(j.factorial:ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hij
  have hi0 : (i.factorial:ℝ)≠0 := by positivity
  have hji0 : ((j-i).factorial:ℝ)≠0 := by positivity
  have hj0 : (j.factorial:ℝ)≠0 := by positivity
  dsimp [normalizedWithin]
  field_simp
  linear_combination iteratedDerivWithin i f s x*iteratedDerivWithin (j-i) g s x*hfac

/--
Exact identity `normalizedWithin (derivWithin f s) s j x=(j+1)*normalizedWithin f s (j+1) x`.

Use: `chebyshev2.Numerics.normalizedWithin_exp` rewrites with this identity to establish
the stated quantitative bound `(j+1)*normalizedWithin (fun t => Real.exp (f t)) s (j+1) x= ∑
i∈Finset.range (j+1),(i+1)*normalizedWithin f s (i+1) x* normalizedWithin (fun t => Real.exp (f
t)) s (j-i) x`.

Article: chebyshev2, Lemma 18 via `chebyshev2.Numerics.normalizedWithin_exp`.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedWithin_deriv {f : ℝ → ℝ} {s : Set ℝ} (j : ℕ) (x : ℝ) :
    normalizedWithin (derivWithin f s) s j x=(j+1)*normalizedWithin f s (j+1) x := by
  simp only [normalizedWithin,← iteratedDerivWithin_succ',Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have h0 : (j.factorial:ℝ)≠0 := by positivity
  have hj0 : (j:ℝ)+1≠0 := by positivity
  field

/--
Exact identity `normalizedWithin (fun _ => c) s j x=0`.

Use: `chebyshev2.Numerics.normalizedWithin_inverse` uses this identity to establish the
stated quantitative bound `normalizedWithin (fun t => (f t)⁻¹) s j x= -(∑ i∈Finset.range
j,normalizedWithin f s (i+1) x* normalizedWithin (fun t => (f t)⁻¹) s (j-(i+1)) x)/f x`.

Article: chebyshev2, Lemma 18 via `chebyshev2.Numerics.normalizedWithin_inverse`.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedWithin_const {s : Set ℝ} {j : ℕ} (hj : 0<j) (c x : ℝ) :
    normalizedWithin (fun _ => c) s j x=0 := by simp [normalizedWithin,iteratedDerivWithin_const,hj.ne']

/--
Exact identity `normalizedWithin (fun t => f t-c) s j x=normalizedWithin f s j x`.

Use: `chebyshev2.Numerics.normalizedWithin_shifted_riccati` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Lemma 18 via `chebyshev2.Numerics.normalizedWithin_shifted_riccati`.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedWithin_sub_const {f : ℝ → ℝ} {s : Set ℝ} {j : ℕ}
    (hj : 0<j) (c x : ℝ) : normalizedWithin (fun t => f t-c) s j x=normalizedWithin f s j x := by
  simp only [normalizedWithin,sub_eq_add_neg]
  have he := iteratedDerivWithin_const_add (f := f) (s := s) (x := x) hj (-c)
  simpa only [add_comm] using congrArg (fun z : ℝ => z/(j.factorial:ℝ)) he

/--
Exact identity `normalizedWithin (fun t => c*f t) s j x=c*normalizedWithin f s j x`.

Use: `chebyshev2.Numerics.normalizedWithin_shifted_riccati` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Lemma 18 via `chebyshev2.Numerics.normalizedWithin_shifted_riccati`.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedWithin_const_mul (f : ℝ → ℝ) (s : Set ℝ) (j : ℕ) (c x : ℝ) :
    normalizedWithin (fun t => c*f t) s j x=c*normalizedWithin f s j x := by
  simp only [normalizedWithin,iteratedDerivWithin_const_mul_field]
  ring

/--
The stated quantitative bound `normalizedWithin (fun t => f t*g t) s (n+1) x= ∑ i∈Finset.range
n,normalizedWithin f s (i+1) x*normalizedWithin g s (n-i) x`.

Use: `chebyshev2.Numerics.normalizedWithin_centered_cube` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Lemma 19 via `chebyshev2.Numerics.positiveCubic_jet_recurrence`.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Use the identities/estimates `chebyshev2.Numerics.normalizedWithin_mul`,
`chebyshev2.Numerics.normalizedWithin_zero` with the arguments shown in the proof.
-/
theorem normalizedWithin_mul_vanishing {f g : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (hf : ContDiffWithinAt ℝ (n+1) f s x) (hg : ContDiffWithinAt ℝ (n+1) g s x)
    (hf0 : f x=0) (hg0 : g x=0) :
    normalizedWithin (fun t => f t*g t) s (n+1) x=
      ∑ i∈Finset.range n,normalizedWithin f s (i+1) x*normalizedWithin g s (n-i) x := by
  -- Use the identities/estimates `chebyshev2.Numerics.normalizedWithin_mul`,
  -- `chebyshev2.Numerics.normalizedWithin_zero` with the arguments shown in the proof.
  rw [normalizedWithin_mul hs hx hf hg,Finset.sum_range_succ,Finset.sum_range_succ']
  simp only [normalizedWithin_zero,hf0,hg0,zero_mul,mul_zero,add_zero,Nat.sub_self,
    show ∀ i : ℕ,n+1-(i+1)=n-i by omega]

/--
The stated quantitative bound `normalizedWithin (fun t => (f t)⁻¹) s j x= -(∑ i∈Finset.range
j,normalizedWithin f s (i+1) x* normalizedWithin (fun t => (f t)⁻¹) s (j-(i+1)) x)/f x`.

Use: `chebyshev2.Numerics.reciprocalJetCheck_encloses` rewrites with this identity to
establish the stated quantitative bound `JetEncloses R (fun t => (f t)⁻¹) s x N`.

Article: chebyshev2, Lemma 18.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Use the identities/estimates `chebyshev2.Numerics.normalizedWithin_mul`,
`chebyshev2.Numerics.normalizedWithin_congr`,
`chebyshev2.Numerics.normalizedWithin_const` with the arguments shown in the proof.
-/
theorem normalizedWithin_inverse {f : ℝ → ℝ} {s : Set ℝ} {j : ℕ} {x : ℝ}
    (hj : 0<j) (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (hf : ContDiffWithinAt ℝ j f s x) (hn : ∀ t∈s,f t≠0) :
    normalizedWithin (fun t => (f t)⁻¹) s j x=
      -(∑ i∈Finset.range j,normalizedWithin f s (i+1) x*
        normalizedWithin (fun t => (f t)⁻¹) s (j-(i+1)) x)/f x := by
  -- Use the identities/estimates `chebyshev2.Numerics.normalizedWithin_mul`,
  -- `chebyshev2.Numerics.normalizedWithin_congr`,
  -- `chebyshev2.Numerics.normalizedWithin_const` with the arguments shown in the proof.
  have hp := normalizedWithin_mul (f := f) (g := fun t => (f t)⁻¹) hs hx hf (hf.inv (hn x hx))
  have hzero : normalizedWithin (fun t => f t*(f t)⁻¹) s j x=0 := by
    rw [normalizedWithin_congr (g := fun _ => 1) (fun t ht => mul_inv_cancel₀ (hn t ht)) j hx]
    exact normalizedWithin_const hj 1 x
  rw [hzero,Finset.sum_range_succ',normalizedWithin_zero,Nat.sub_zero] at hp
  apply (eq_div_iff (hn x hx)).mpr
  linarith

/--
The stated quantitative bound `normalizedWithin (fun t => Real.sqrt (f t)) s (n+1) x=
(normalizedWithin f s (n+1) x- ∑ i∈Finset.range n,normalizedWithin (fun t => Real.sqrt (f t)) s
(i+1) x* normalizedWithin (fun t => Real.sqrt (f t)) s (n-i) x)/(2*Real.sqrt (f x))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 18.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Use the identities/estimates `chebyshev2.Numerics.normalizedWithin_mul`,
`chebyshev2.Numerics.normalizedWithin_congr`,
`chebyshev2.Numerics.normalizedWithin_zero` with the arguments shown in the proof.
-/
theorem normalizedWithin_sqrt {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (hf : ContDiffWithinAt ℝ (n+1) f s x) (hp : ∀ t∈s,0<f t) :
    normalizedWithin (fun t => Real.sqrt (f t)) s (n+1) x=
      (normalizedWithin f s (n+1) x-
        ∑ i∈Finset.range n,normalizedWithin (fun t => Real.sqrt (f t)) s (i+1) x*
          normalizedWithin (fun t => Real.sqrt (f t)) s (n-i) x)/(2*Real.sqrt (f x)) := by
  -- Use the identities/estimates `chebyshev2.Numerics.normalizedWithin_mul`,
  -- `chebyshev2.Numerics.normalizedWithin_congr`,
  -- `chebyshev2.Numerics.normalizedWithin_zero` with the arguments shown in the proof.
  let z := fun t => Real.sqrt (f t)
  have hz : ContDiffWithinAt ℝ (n+1) z s x := hf.sqrt (ne_of_gt (hp x hx))
  have he := normalizedWithin_mul hs hx hz hz
  have heq : normalizedWithin (fun t => z t*z t) s (n+1) x=normalizedWithin f s (n+1) x := by
    apply normalizedWithin_congr _ (n+1) hx
    intro t ht
    exact Real.mul_self_sqrt (hp t ht).le
  rw [heq,Finset.sum_range_succ,Finset.sum_range_succ',normalizedWithin_zero] at he
  simp only [Nat.sub_zero,Nat.sub_self,normalizedWithin_zero,
    show ∀ i : ℕ,n+1-(i+1)=n-i by omega] at he
  apply (eq_div_iff (mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr (hp x hx))))).mpr
  dsimp only [z] at he
  nlinarith [he]

/--
The stated quantitative bound `(j+1)*normalizedWithin (fun t => Real.exp (f t)) s (j+1) x= ∑
i∈Finset.range (j+1),(i+1)*normalizedWithin f s (i+1) x* normalizedWithin (fun t => Real.exp (f
t)) s (j-i) x`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 18.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem normalizedWithin_exp {f : ℝ → ℝ} {s : Set ℝ} {j : ℕ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s) (hf : ContDiffOn ℝ (j+1) f s) :
    (j+1)*normalizedWithin (fun t => Real.exp (f t)) s (j+1) x=
      ∑ i∈Finset.range (j+1),(i+1)*normalizedWithin f s (i+1) x*
        normalizedWithin (fun t => Real.exp (f t)) s (j-i) x := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hfd := hf.differentiableOn (by simp)
  have hd : EqOn (derivWithin (fun t => Real.exp (f t)) s)
      (fun t => derivWithin f s t*Real.exp (f t)) s := by
    intro t ht
    have h := ((hfd t ht).hasDerivWithinAt.exp).derivWithin (hs t ht)
    simpa only [mul_comm] using h
  rw [← normalizedWithin_deriv,normalizedWithin_congr hd j hx,
    normalizedWithin_mul hs hx (hf.derivWithin hs (by simp) x hx)
      ((hf.of_le (by simp)).exp x hx)]
  apply Finset.sum_congr rfl
  intro i _
  rw [normalizedWithin_deriv]

/--
Exact identity `(j+1)*normalizedWithin y s (j+1) x=normalizedWithin C s j x+ (∑ i∈Finset.range
(j+1),normalizedWithin A s i x*normalizedWithin y s (j-i) x)+ ∑ i∈Finset.range
(j+1),normalizedWithin B s i x* ∑ k∈Finset.range (j-i+1),normalizedWithin y s k
x*normalizedWithin y s (j-i-k) x`.

Use: `chebyshev2.Numerics.normalizedWithin_shifted_riccati` uses this identity to establish
the identity stated in that declaration.

Article: chebyshev2, Lemma 18.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem normalizedWithin_riccati {C A B y : ℝ → ℝ} {s : Set ℝ} {j : ℕ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (hC : ContDiffWithinAt ℝ j C s x) (hA : ContDiffWithinAt ℝ j A s x)
    (hB : ContDiffWithinAt ℝ j B s x) (hy : ContDiffWithinAt ℝ j y s x)
    (hd : ∀ t∈s,HasDerivWithinAt y (C t+A t*y t+B t*y t^2) s t) :
    (j+1)*normalizedWithin y s (j+1) x=normalizedWithin C s j x+
      (∑ i∈Finset.range (j+1),normalizedWithin A s i x*normalizedWithin y s (j-i) x)+
      ∑ i∈Finset.range (j+1),normalizedWithin B s i x*
        ∑ k∈Finset.range (j-i+1),normalizedWithin y s k x*normalizedWithin y s (j-i-k) x := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [← normalizedWithin_deriv]
  rw [normalizedWithin_congr (fun t ht => (hd t ht).derivWithin (hs t ht)) j hx]
  rw [normalizedWithin_add hs hx (hC.add (hA.mul hy)) (hB.mul (hy.pow 2)),
    normalizedWithin_add hs hx hC (hA.mul hy),normalizedWithin_mul hs hx hA hy,
    normalizedWithin_mul hs hx hB (hy.pow 2)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hij : j-i≤j := Nat.sub_le _ _
  rw [show (fun t => y t^2)=(fun t => y t*y t) by ext t;ring,
    normalizedWithin_mul hs hx (hy.of_le (by exact_mod_cast hij)) (hy.of_le (by exact_mod_cast hij))]

/--
The stated quantitative bound `(j+1)*normalizedWithin y s (j+1) x= (normalizedWithin C s j
x+normalizedWithin A s j x*c+normalizedWithin B s j x*c^2)+ (∑ i∈Finset.range
(j+1),(normalizedWithin A s i x+2*normalizedWithin B s i x*c)* normalizedWithin (fun t => y
t-c) s (j-i) x)+ ∑ i∈Finset.range (j+1),normalizedWithin B s i x* ∑ k∈Finset.range
(j-i+1),normalizedWithin (fun t => y t-c) s k x* normalizedWithin (fun t => y t-c) s (j-i-k)
x`.

Use: `chebyshev2.Numerics.riccatiJetCheck_sound` uses this identity to establish
establishes the uniform, quantified assertion `∀ j≤N,normalizedWithin (fun t => y t-y x) s j
x∈jetAt R j`.

Article: chebyshev2, Lemma 18.

Source: Griewank and Walther, Evaluating Derivatives — normalized Taylor derivative
recurrences.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem normalizedWithin_shifted_riccati {C A B y : ℝ → ℝ} {s : Set ℝ} {j : ℕ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (hC : ContDiffWithinAt ℝ j C s x) (hA : ContDiffWithinAt ℝ j A s x)
    (hB : ContDiffWithinAt ℝ j B s x) (hy : ContDiffWithinAt ℝ j y s x)
    (hd : ∀ t∈s,HasDerivWithinAt y (C t+A t*y t+B t*y t^2) s t) (c : ℝ) :
    (j+1)*normalizedWithin y s (j+1) x=
      (normalizedWithin C s j x+normalizedWithin A s j x*c+normalizedWithin B s j x*c^2)+
      (∑ i∈Finset.range (j+1),(normalizedWithin A s i x+2*normalizedWithin B s i x*c)*
        normalizedWithin (fun t => y t-c) s (j-i) x)+
      ∑ i∈Finset.range (j+1),normalizedWithin B s i x*
        ∑ k∈Finset.range (j-i+1),normalizedWithin (fun t => y t-c) s k x*
          normalizedWithin (fun t => y t-c) s (j-i-k) x := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hρ : ContDiffWithinAt ℝ j (fun t => y t-c) s x := hy.sub contDiffWithinAt_const
  have hCs : ContDiffWithinAt ℝ j (fun t => C t+A t*c+B t*c^2) s x := (hC.add (hA.mul contDiffWithinAt_const)).add
    (hB.mul contDiffWithinAt_const)
  have hAs : ContDiffWithinAt ℝ j (fun t => A t+2*B t*c) s x := hA.add ((contDiffWithinAt_const.mul hB).mul contDiffWithinAt_const)
  have he := normalizedWithin_riccati (y := fun t => y t-c)
    (C := fun t => C t+A t*c+B t*c^2) (A := fun t => A t+2*B t*c) (B := B)
    hs hx hCs hAs hB hρ (fun t ht => by convert (hd t ht).sub_const c using 1;ring)
  rw [normalizedWithin_sub_const (by omega)] at he
  rw [normalizedWithin_add hs hx (hC.add (hA.mul contDiffWithinAt_const))
      (hB.mul contDiffWithinAt_const),
    normalizedWithin_add hs hx hC (hA.mul contDiffWithinAt_const)] at he
  have hmul (f : ℝ → ℝ) (n : ℕ) (d : ℝ) :
      normalizedWithin (fun t => f t*d) s n x=normalizedWithin f s n x*d := by
    simpa only [mul_comm] using normalizedWithin_const_mul f s n d x
  rw [hmul,hmul] at he
  convert he using 1
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i≤j := by have := Finset.mem_range.mp hi;omega
  rw [normalizedWithin_add hs hx (hA.of_le (by exact_mod_cast hil))
    (((contDiffWithinAt_const.mul hB).mul contDiffWithinAt_const).of_le (by exact_mod_cast hil)),hmul,
    normalizedWithin_const_mul]

end
end chebyshev2.Numerics
