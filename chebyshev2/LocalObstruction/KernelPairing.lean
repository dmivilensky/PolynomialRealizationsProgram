import chebyshev2.Continuum.KernelSquareIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
Article: chebyshev2, Theorem 6.1.
The signed bilinear kernel pairing underlying Lemma 26(iii).
Use: `chebyshev2.LocalObstruction.pairing_variation` feeds
`chebyshev2.LocalObstruction.theorem_6_1` (theorem 6 1).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set Real MeasureTheory Filter chebyshev2.Continuum
set_option backward.isDefEq.respectTransparency false

/--
Defines `W₂` of type `ℝ` by `∫ y, m y*exp (-2*|x-y|)`.

Use: `chebyshev2.LocalObstruction.W₂_add` uses this definition to establish the identity
`W₂ (a+b) x=W₂ a x+W₂ b x`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def W₂ (m : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, m y*exp (-2*|x-y|)
/--
Defines `pairing` of type `ℝ` by `∫ x, a x*W₂ b x`.

Use: `chebyshev2.LocalObstruction.pairing_add_left` uses this definition to establish exact
identity `pairing (a+b) c=pairing a c+pairing b c`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def pairing (a b : ℝ → ℝ) : ℝ := ∫ x, a x*W₂ b x

/--
The stated quantitative bound `exp (-2*|x-y|) ≤ 1`.

Use: `chebyshev2.LocalObstruction.W₂_continuous` uses this bound to establish continuity of
the displayed function: `Continuous (W₂ m)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem kernel_bound (x y : ℝ) : exp (-2*|x-y|) ≤ 1 :=
  exp_le_one_iff.mpr (by have := abs_nonneg (x-y); linarith)

/--
Integrability of the displayed function: `Integrable (fun y => m y*exp (-2*|x-y|))`.

Use: `chebyshev2.LocalObstruction.W₂_add` uses this integrability result to establish exact
identity `W₂ (a+b) x=W₂ a x+W₂ b x`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.kernel_bound` with the
arguments shown in the proof.
-/
theorem W₂_integrable {m : ℝ → ℝ} (hm : Integrable m) (x : ℝ) :
    Integrable (fun y => m y*exp (-2*|x-y|)) := by
  apply hm.norm.mono'
  · exact hm.aestronglyMeasurable.mul (by fun_prop : Continuous
      (fun y : ℝ => exp (-2*|x-y|))).aestronglyMeasurable
  · exact Eventually.of_forall (fun y => by
      rw [norm_mul,Real.norm_of_nonneg (exp_pos _).le]
      exact mul_le_of_le_one_right (norm_nonneg _) (kernel_bound x y))

/--
Continuity of the displayed function: `Continuous (W₂ m)`.

Use: `chebyshev2.LocalObstruction.traceGradient` uses this continuity result in the
displayed construction of `traceGradient`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.W₂_integrable`,
`chebyshev2.LocalObstruction.kernel_bound` with the arguments shown in the proof.
-/
theorem W₂_continuous {m : ℝ → ℝ} (hm : Integrable m) : Continuous (W₂ m) := by
  -- Apply the dominated-convergence/Lp transfer after supplying the domination and
  -- pointwise-limit hypotheses.
  rw [continuous_iff_continuousAt]
  intro x
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖m y‖)
  · exact Eventually.of_forall (fun z => (W₂_integrable hm z).aestronglyMeasurable)
  · exact Eventually.of_forall (fun z => Eventually.of_forall (fun y => by
      rw [norm_mul,Real.norm_of_nonneg (exp_pos _).le]
      exact mul_le_of_le_one_right (norm_nonneg _) (kernel_bound z y)))
  · exact hm.norm
  · exact Eventually.of_forall (fun y => (by fun_prop :
      Continuous (fun z : ℝ => m y*exp (-2*|z-y|))).continuousAt.tendsto)

/--
Integrability of the displayed function: `Integrable (fun p : ℝ × ℝ => a p.1*b p.2*exp
(-2*|p.1-p.2|)) (volume.prod volume)`.

Use: `chebyshev2.LocalObstruction.pairing_integrable` uses this integrability result to
establish integrability of the displayed function: `Integrable (fun x => a x*W₂ b x)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.kernel_bound` with the
arguments shown in the proof.
-/
theorem pair_integrable {a b : ℝ → ℝ} (ha : Integrable a) (hb : Integrable b) :
    Integrable (fun p : ℝ × ℝ => a p.1*b p.2*exp (-2*|p.1-p.2|)) (volume.prod volume) := by
  -- Use the identities/estimates `chebyshev2.LocalObstruction.kernel_bound` with the
  -- arguments shown in the proof.
  apply (ha.norm.mul_prod hb.norm).mono'
  · exact ((ha.aestronglyMeasurable.comp_fst).mul
      hb.aestronglyMeasurable.comp_snd).mul
      (by fun_prop : Continuous (fun p : ℝ × ℝ => exp (-2*|p.1-p.2|))).aestronglyMeasurable
  · exact Eventually.of_forall (fun p => by
      rw [norm_mul,norm_mul,Real.norm_of_nonneg (exp_pos _).le]
      exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (kernel_bound p.1 p.2))

/--
Integrability of the displayed function: `Integrable (fun x => a x*W₂ b x)`.

Use: `chebyshev2.LocalObstruction.pairing_add_left` uses this integrability result to
establish exact identity `pairing (a+b) c=pairing a c+pairing b c`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Establish the required integrability/summability obligations before exchanging integrals
or sums. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem pairing_integrable {a b : ℝ → ℝ} (ha : Integrable a) (hb : Integrable b) :
    Integrable (fun x => a x*W₂ b x) := by
  convert (pair_integrable ha hb).integral_prod_left using 1
  funext x
  rw [W₂,← integral_const_mul]
  congr 1
  funext y
  ring

/--
Exact identity `pairing a b=pairing b a`.

Use: `chebyshev2.LocalObstruction.pairing_add_right` rewrites with this identity to
establish exact identity `pairing a (b+c)=pairing a b+pairing a c`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Establish the required integrability/summability obligations before exchanging integrals
or sums. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem pairing_symm {a b : ℝ → ℝ} (ha : Integrable a) (hb : Integrable b) :
    pairing a b=pairing b a := by
  -- Establish the required integrability/summability obligations before exchanging integrals
  -- or sums.
  have he (a b : ℝ → ℝ) : pairing a b=∫ x, ∫ y, a x*b y*exp (-2*|x-y|) := by
    unfold pairing W₂
    congr 1
    funext x
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  rw [he a b,integral_integral_swap (pair_integrable ha hb),he b a]
  congr 1
  funext y
  congr 1
  funext x
  rw [abs_sub_comm]
  ring

/--
Exact identity `W₂ (a+b) x=W₂ a x+W₂ b x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.W₂_integrable` with the
arguments shown in the proof.
-/
theorem W₂_add {a b : ℝ → ℝ} (ha : Integrable a) (hb : Integrable b) (x : ℝ) :
    W₂ (a+b) x=W₂ a x+W₂ b x := by
  unfold W₂
  simp only [Pi.add_apply,add_mul]
  exact integral_add (W₂_integrable ha x) (W₂_integrable hb x)

/--
Exact identity `W₂ (c • a) x=c*W₂ a x`.

Use: `chebyshev2.LocalObstruction.pairing_smul_right` rewrites with this identity to
establish exact identity `pairing a (c • b)=c*pairing a b`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem W₂_smul (c : ℝ) (a : ℝ → ℝ) (x : ℝ) : W₂ (c • a) x=c*W₂ a x := by
  unfold W₂
  simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]

/--
Exact identity `pairing (a+b) c=pairing a c+pairing b c`.

Use: `chebyshev2.LocalObstruction.pairing_add_right` rewrites with this identity to
establish exact identity `pairing a (b+c)=pairing a b+pairing a c`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.pairing_integrable` with
the arguments shown in the proof.
-/
theorem pairing_add_left {a b c : ℝ → ℝ} (ha : Integrable a) (hb : Integrable b)
    (hc : Integrable c) : pairing (a+b) c=pairing a c+pairing b c := by
  unfold pairing
  simp only [Pi.add_apply,add_mul]
  exact integral_add (pairing_integrable ha hc) (pairing_integrable hb hc)

/--
Exact identity `pairing (c • a) b=c*pairing a b`.

Use: `chebyshev2.LocalObstruction.pairing_quadratic` rewrites with this identity to
establish exact identity `pairing (m+ε • v) (m+ε • v)=pairing m m+2*ε*pairing v m+ε^2*pairing v
v`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem pairing_smul_left (c : ℝ) (a b : ℝ → ℝ) : pairing (c • a) b=c*pairing a b := by
  unfold pairing
  simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]

/--
Exact identity `pairing a (b+c)=pairing a b+pairing a c`.

Use: `chebyshev2.LocalObstruction.pairing_quadratic` rewrites with this identity to
establish exact identity `pairing (m+ε • v) (m+ε • v)=pairing m m+2*ε*pairing v m+ε^2*pairing v
v`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.pairing_symm`,
`chebyshev2.LocalObstruction.pairing_add_left` with the arguments shown in the proof.
-/
theorem pairing_add_right {a b c : ℝ → ℝ} (ha : Integrable a) (hb : Integrable b)
    (hc : Integrable c) : pairing a (b+c)=pairing a b+pairing a c := by
  rw [pairing_symm ha (hb.add hc),pairing_add_left hb hc ha,
    pairing_symm hb ha,pairing_symm hc ha]

/--
Exact identity `pairing a (c • b)=c*pairing a b`.

Use: `chebyshev2.LocalObstruction.pairing_quadratic` rewrites with this identity to
establish exact identity `pairing (m+ε • v) (m+ε • v)=pairing m m+2*ε*pairing v m+ε^2*pairing v
v`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.W₂_smul` with the
arguments shown in the proof.
-/
theorem pairing_smul_right (c : ℝ) (a b : ℝ → ℝ) : pairing a (c • b)=c*pairing a b := by
  unfold pairing
  simp only [W₂_smul]
  simp_rw [mul_left_comm (a _) c,integral_const_mul]

/--
Exact identity `pairing (m+ε • v) (m+ε • v)=pairing m m+2*ε*pairing v m+ε^2*pairing v v`.

Use: `chebyshev2.LocalObstruction.pairing_variation` uses this identity to establish the
actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => pairing (m+ε • v) (m+ε • v))
(2*∫ x, v x*W₂ m x) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.pairing_add_left`,
`chebyshev2.LocalObstruction.pairing_add_right`,
`chebyshev2.LocalObstruction.pairing_smul_left` with the arguments shown in the proof.
-/
theorem pairing_quadratic {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v) (ε : ℝ) :
    pairing (m+ε • v) (m+ε • v)=pairing m m+2*ε*pairing v m+ε^2*pairing v v := by
  rw [pairing_add_left hm (hv.smul ε) (hm.add (hv.smul ε)),
    pairing_add_right hm hm (hv.smul ε),pairing_add_right (hv.smul ε) hm (hv.smul ε),
    pairing_smul_left,pairing_smul_left,pairing_smul_right,pairing_smul_right,
    pairing_symm hm hv]
  ring

/--
The actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => pairing (m+ε • v) (m+ε •
v)) (2*∫ x, v x*W₂ m x) 0`.

Use: `chebyshev2.LocalObstruction.traceObservationWitness` uses this derivative formula in
the displayed construction of `traceObservationWitness`. Its inputs and component formulas are
fixed by that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem pairing_variation {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v) :
    HasDerivAt (fun ε : ℝ => pairing (m+ε • v) (m+ε • v))
      (2*∫ x, v x*W₂ m x) 0 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : (fun ε : ℝ => pairing (m+ε • v) (m+ε • v))=
      (fun ε => pairing m m+2*ε*pairing v m+ε^2*pairing v v) :=
    funext (pairing_quadratic hm hv)
  rw [he]
  convert! ((hasDerivAt_const 0 (pairing m m)).add
    (((hasDerivAt_id 0).const_mul 2).mul_const (pairing v m))).add
      (((hasDerivAt_id 0).pow 2).mul_const (pairing v v)) using 1
  simp [pairing]

/--
Exact identity `pairing m m=∑' j, kernelEigenvalue hm hn j^2`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem pairing_eq_spectral_square {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    pairing m m=∑' j, kernelEigenvalue hm hn j^2 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  rw [kernelEigenvalue_square_integral hm hn]
  unfold pairing W₂
  congr 1
  funext x
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

end
end chebyshev2.LocalObstruction
