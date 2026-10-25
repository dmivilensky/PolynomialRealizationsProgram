import chebyshev2.LocalObstruction.ObservationWitness

/-!
Article: chebyshev2, Theorem 6.1.
Finite linear combinations preserve the exact two-term sine tail.
Use: `chebyshev2.LocalObstruction.TailGradient.sum` feeds
`chebyshev2.LocalObstruction.finite_observation_no_local_bound_with_property` (finite
observation no local bound with property).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Real Filter Asymptotics chebyshev2.SineContinuum
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

 /--
Constructs `TailGradient.smul` of type `TailGradient` by the displayed record fields. Data
fields specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.LocalObstruction.sObservationWitness` uses this definition in the
displayed construction of `sObservationWitness`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.
-/
def TailGradient.smul (g : TailGradient) (a : ℝ) : TailGradient where
  value x := a*g.value x
  continuous := continuous_const.mul g.continuous
  constant := a*g.constant
  exponential := a*g.exponential
  tail := by
    have h := g.tail.const_mul_left a
    convert! h using 1
    funext x
    ring

 /--
Constructs `TailGradient.add` of type `TailGradient` by the displayed record fields. Data
fields specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.LocalObstruction.sObservationWitness` uses this definition in the
displayed construction of `sObservationWitness`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def TailGradient.add (g h : TailGradient) : TailGradient where
  value x := g.value x+h.value x
  continuous := g.continuous.add h.continuous
  constant := g.constant+h.constant
  exponential := g.exponential+h.exponential
  tail := by
    have ht := g.tail.add h.tail
    convert! ht using 1
    funext x
    ring

 /--
Constructs `TailGradient.sum` of type `TailGradient` by the displayed record fields. Data
fields specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.LocalObstruction.finite_observation_no_local_bound_with_property` uses
this definition to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def TailGradient.sum {ι : Type*} [Fintype ι] (g : ι → TailGradient) (a : ι → ℝ) : TailGradient where
  value x := ∑ i,a i*(g i).value x
  continuous := continuous_finsetSum _ (fun i _ => continuous_const.mul (g i).continuous)
  constant := ∑ i,a i*(g i).constant
  exponential := ∑ i,a i*(g i).exponential
  tail := by
    have h := Asymptotics.IsLittleO.sum (s := Finset.univ)
      (fun i _ => (g i).tail.const_mul_left (a i))
    convert! h using 1
    funext x
    rw [Finset.sum_apply]
    change (∑ i,a i*(g i).value x)-(∑ i,a i*(g i).constant)-
      (∑ i,a i*(g i).exponential)*exp (-2*x)=
        ∑ i,a i*((g i).value x-(g i).constant-(g i).exponential*exp (-2*x))
    simp_rw [mul_sub,← mul_assoc]
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,Finset.sum_mul]

end
end chebyshev2.LocalObstruction
