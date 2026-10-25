import chebyshev2.Numerics.BoxMaxima
import chebyshev2.Residual.SmoothConjugate
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
Article: chebyshev2, Lemma 24.
Actual multivariable first and second derivatives for F.2.
Use: `chebyshev2.Numerics.StateJetOn` feeds
`chebyshev2.Numerics.StateJetOn.segment_taylor_upper` (segment taylor upper).
Proof chain: `chebyshev2.Numerics.StateJetOn.segment_first_order_upper` — chebyshev2, Lemma
24; Actual multivariable segment, state and time Taylor/concavity upper bounds.
-/
namespace chebyshev2.Numerics
noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Defines `gradientMap` of type `(Fin d → ℝ) →L[ℝ] ℝ` by `∑ i,g i • ContinuousLinearMap.proj i`.

Use: `chebyshev2.Numerics.gradientMap_apply` rewrites with this definition to establish
exact identity `gradientMap g v=∑ i,g i*v i`.

Article: chebyshev2, Lemma 24 via
`chebyshev2.Numerics.StateJetOn.segment_first_order_upper`.
-/
def gradientMap {d : ℕ} (g : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ i,g i • ContinuousLinearMap.proj i

/--
Exact identity `gradientMap g v=∑ i,g i*v i`.

Use: `chebyshev2.Numerics.StateJetOn.compose` uses this identity in the displayed
construction of `compose`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 24 via
`chebyshev2.Numerics.StateJetOn.segment_first_order_upper`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem gradientMap_apply {d : ℕ} (g v : Fin d → ℝ) : gradientMap g v=∑ i,g i*v i := by simp [gradientMap]

/--
Exact identity `gradientMap (fun i => a*g i+b*h i)=a • gradientMap g+b • gradientMap h`.

Use: `chebyshev2.Numerics.StateJetOn.add` uses this identity in the displayed construction
of `add`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 24.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem gradientMap_linear {d : ℕ} (g h : Fin d → ℝ) (a b : ℝ) :
    gradientMap (fun i => a*g i+b*h i)=a • gradientMap g+b • gradientMap h := by
  ext v
  simp [gradientMap,add_mul,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]

/--
An actual scalar state function together with its gradient/Hessian and proofs of the
corresponding Fréchet derivative formulas on the declared domain.

Use: `chebyshev2.Numerics.StateJetOn.add` uses this record of data and proof obligations in
the displayed construction of `add`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 24 via
`chebyshev2.Numerics.StateJetOn.segment_first_order_upper`.
-/
structure StateJetOn {d : ℕ} (s : Set (Fin d → ℝ)) where
  /-- Scalar function on the finite-dimensional state space. -/
  value : (Fin d → ℝ) → ℝ
  /-- Coordinate gradient of that actual function. -/
  gradient : (Fin d → ℝ) → Fin d → ℝ
  /-- Coordinate Hessian of the actual gradient. -/
  hessian : (Fin d → ℝ) → Fin d → Fin d → ℝ
  /-- The stated gradient is the Fréchet derivative within the declared state domain. -/
  value_derivative : ∀ x∈s,HasFDerivWithinAt value (gradientMap (gradient x)) s x
  /-- Each gradient component has the stated Hessian row as its derivative within that domain. -/
  gradient_derivative : ∀ x∈s,∀ i,HasFDerivWithinAt (fun y => gradient y i)
    (gradientMap (hessian x i)) s x

namespace StateJetOn
variable {d : ℕ} {s : Set (Fin d → ℝ)}

/--
Constructs `add` of type `StateJetOn s` by the displayed record fields. Data fields specify the
construction; proof fields discharge its required properties.

Use: `chebyshev2.Numerics.StateIntervalJet.encloses_add` uses this definition to establish
the precise assertion is `(J.add K).Encloses (F.add G)`.

Article: chebyshev2, Lemma 24.
-/
def add (F G : StateJetOn s) : StateJetOn s where
  value x := F.value x+G.value x
  gradient x i := F.gradient x i+G.gradient x i
  hessian x i j := F.hessian x i j+G.hessian x i j
  value_derivative x hx := by
    have he := gradientMap_linear (F.gradient x) (G.gradient x) 1 1
    simp only [one_mul,one_smul] at he
    rw [he]
    exact (F.value_derivative x hx).add (G.value_derivative x hx)
  gradient_derivative x hx i := by
    have he := gradientMap_linear (F.hessian x i) (G.hessian x i) 1 1
    simp only [one_mul,one_smul] at he
    rw [he]
    exact (F.gradient_derivative x hx i).add (G.gradient_derivative x hx i)

/--
Constructs `mul` of type `StateJetOn s` by the displayed record fields. Data fields specify the
construction; proof fields discharge its required properties.

Use: `chebyshev2.Numerics.StateIntervalJet.encloses_mul` uses this definition to establish
the precise assertion is `(J.mul K).Encloses (F.mul G)`.

Article: chebyshev2, Lemma 24.
-/
def mul (F G : StateJetOn s) : StateJetOn s where
  value x := F.value x*G.value x
  gradient x i := F.gradient x i*G.value x+F.value x*G.gradient x i
  hessian x i j := F.hessian x i j*G.value x+F.gradient x i*G.gradient x j+
    F.gradient x j*G.gradient x i+F.value x*G.hessian x i j
  value_derivative x hx := by
    have he : gradientMap (fun i => F.gradient x i*G.value x+F.value x*G.gradient x i)=
        F.value x • gradientMap (G.gradient x)+G.value x • gradientMap (F.gradient x) := by
      simpa only [mul_comm,add_comm] using
        gradientMap_linear (F.gradient x) (G.gradient x) (G.value x) (F.value x)
    rw [he]
    exact (F.value_derivative x hx).mul (G.value_derivative x hx)
  gradient_derivative x hx i := by
    have h := ((F.gradient_derivative x hx i).mul (G.value_derivative x hx)).add
      ((F.value_derivative x hx).mul (G.gradient_derivative x hx i))
    convert! h using 1
    ext v
    simp only [add_apply,smul_apply,smul_eq_mul,gradientMap_apply]
    simp_rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring

/--
Constructs `compose` of type `StateJetOn s` by the displayed record fields. Data fields specify
the construction; proof fields discharge its required properties.

Use: `chebyshev2.Numerics.StateJetOn.inverse` uses this definition in the displayed
construction of `inverse`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 24.
-/
def compose (F : StateJetOn s) (φ φ₁ φ₂ : ℝ → ℝ)
    (hφ : ∀ x∈s,HasDerivAt φ (φ₁ (F.value x)) (F.value x))
    (hφ₁ : ∀ x∈s,HasDerivAt φ₁ (φ₂ (F.value x)) (F.value x)) : StateJetOn s where
  value x := φ (F.value x)
  gradient x i := φ₁ (F.value x)*F.gradient x i
  hessian x i j := φ₂ (F.value x)*F.gradient x i*F.gradient x j+
    φ₁ (F.value x)*F.hessian x i j
  value_derivative x hx := by
    have h := (hφ x hx).comp_hasFDerivWithinAt x (F.value_derivative x hx)
    convert! h using 1
    ext v
    simp [gradientMap,Finset.mul_sum,mul_assoc]
  gradient_derivative x hx i := by
    have h := ((hφ₁ x hx).comp_hasFDerivWithinAt x (F.value_derivative x hx)).mul
      (F.gradient_derivative x hx i)
    convert! h using 1
    ext v
    simp only [add_apply,smul_apply,smul_eq_mul,gradientMap_apply,Function.comp_apply]
    simp_rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring

/--
Defines `psi` of type `StateJetOn s`. The displayed construction fixes its component data; its
proof fields enforce the listed compatibility properties.

Use: `chebyshev2.Numerics.StateIntervalJet.encloses_psi` uses this definition to establish
the precise assertion is `J.psi.Encloses F.psi`.

Article: chebyshev2, Lemma 24.
-/
def psi (F : StateJetOn s) : StateJetOn s :=
  F.compose chebyshev2.Residual.psi
    (fun t => -1+4/9*(max (t+3/2) 0)^2) (fun t => 8/9*max (t+3/2) 0)
    (fun x _ => chebyshev2.Residual.psi_derivative (F.value x))
    (fun x _ => by
      have he : deriv chebyshev2.Residual.psi=(fun t => -1+4/9*(max (t+3/2) 0)^2) :=
        funext (fun t => (chebyshev2.Residual.psi_derivative t).deriv)
      rw [← he]
      exact chebyshev2.Residual.psi_second_derivative (F.value x))

/--
Defines `inverse` of type `StateJetOn s` by `F.compose (fun t => t⁻¹) (fun t => -(t⁻¹)^2) (fun
t => 2*(t⁻¹)^3) (fun x hx => by simpa only [one_div,inv_pow] using hasDerivAt_inv (hn x hx))
(fun x hx => by have h := ((hasDerivAt_inv (hn x hx)).pow 2).neg convert! h using 1 simp only
[Nat.cast_ofNat,inv_pow] ring)`.

Use: `chebyshev2.Numerics.StateIntervalJet.encloses_inverse` rewrites with this definition
to establish `K.Encloses (F.inverse hn)`.

Article: chebyshev2, Lemma 24.
-/
def inverse (F : StateJetOn s) (hn : ∀ x∈s,F.value x≠0) : StateJetOn s :=
  F.compose (fun t => t⁻¹) (fun t => -(t⁻¹)^2) (fun t => 2*(t⁻¹)^3)
    (fun x hx => by simpa only [one_div,inv_pow] using hasDerivAt_inv (hn x hx))
    (fun x hx => by
      have h := ((hasDerivAt_inv (hn x hx)).pow 2).neg
      convert! h using 1
      simp only [Nat.cast_ofNat,inv_pow]
      ring)

end StateJetOn
end
end chebyshev2.Numerics
