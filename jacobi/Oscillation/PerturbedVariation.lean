import jacobi.Oscillation.InverseSquareVariation

/-!
Article: jacobi, Proposition B.1.
The actual two phase equations, literal C1 perturbation bounds and a
true small initial phase difference imply a uniform integrated corrected
phase estimate over the entire growing comparison interval. The result
uses the proved linear barrier and exact invariant derivatives, rather
than an assumed averaged phase identity.
Use: the actual scaled Jacobi and Bessel phase construction supplies these original ODE inputs for the sharp angular estimate of Proposition B.1 (a).
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The genuine perturbed and unperturbed corrected phases have a uniform integrated difference, with no logarithmic or exponential loss on the growing interval.
Use: the actual scaled Jacobi and Bessel phase construction supplies these original ODE inputs for the sharp angular estimate of Proposition B.1 (a).
Article: jacobi, Proposition B.1.
Proof: the true phase equations and initial discrepancy give the proved
linear phase bound. The exact derivative identities and literal C1
perturbation bounds then give the integrable majorant
K*epsilon*(x^(-2)+N^(-1)). Fence its true primitive on the full interval
ending at most L*N. No asymptotic phase or averaged error is a premise. -/
theorem perturbedInvariant_variation {f g e e' P : ℝ → ℝ} {c epsilon B a y N L : ℝ}
    (ha : 1≤a) (hlarge : 4*|c|≤a) (hay : a≤y) (hN : 0<N) (hy : y≤L*N)
    (heps : 0<epsilon) (hepsN : epsilon≤1/N) (hB : 2<B)
    (hf : ∀ x∈Icc a y,HasDerivAt f (1+(c/x^2+e x)*sin (f x)^2) x)
    (hg : ∀ x∈Icc a y,HasDerivAt g (1+c/x^2*sin (g x)^2) x)
    (he : ∀ x∈Icc a y,HasDerivAt e (e' x) x)
    (hP : ∀ x∈Icc a y,HasDerivAt P (e x) x)
    (hebound : ∀ x∈Icc a y,|e x|≤epsilon)
    (he'bound : ∀ x∈Icc a y,|e' x|≤epsilon/N)
    (hinit : |f a-g a|≤B*epsilon*a) :
    |(perturbedInvariant c f e P y-phaseInvariant c g y)-
      (perturbedInvariant c f e P a-phaseInvariant c g a)|≤
      (((4*c^2+2*|c|)*B+2*|c|+1)*epsilon)*(1+L) := by
  -- The actual ODE derivatives, rather than a claimed finite approximation certificate, feed both the phase barrier and the invariant majorant.
  let K := (4*c^2+2*|c|)*B+2*|c|+1
  let F := fun x => perturbedInvariant c f e P x-phaseInvariant c g x
  let F' := fun x => perturbedInvariantSlope c f e e' x-phaseInvariantSlope c g x
  have ha0 : 0<a := by linarith
  have hB0 : 0≤B := by linarith
  have hphase := phase_linear_perturbation ha0 hlarge heps hB hf hg hebound hinit
  have hK : 0≤K := by dsimp [K]; positivity
  have hder : ∀ x∈Icc a y,HasDerivAt F (F' x) x := by
    intro x hx
    have hx0 : 0<x := ha0.trans_le hx.1
    exact (perturbedInvariant_hasDerivAt hx0 (hf x hx) (he x hx) (hP x hx)).sub
      (phaseInvariant_hasDerivAt hx0 (hg x hx))
  have hbound : ∀ x∈Icc a y,|F' x|≤(K*epsilon)/x^2+(K*epsilon)/N := by
    intro x hx
    have hh := perturbedInvariant_majorant c f g e e' (ha.trans hx.1) hN heps hB0 hepsN
      (hphase x hx) (hebound x hx) (he'bound x hx)
    convert hh using 1
    dsimp [K]
    ring
  have h := inverseSquare_variation ha hay hN hy (mul_nonneg hK heps.le)
    (mul_nonneg hK heps.le) hder hbound
  convert h using 1
  ring

end
end jacobi.Oscillation
