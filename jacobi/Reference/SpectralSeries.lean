import jacobi.Reference.WaveAnalytic
import jacobi.Reference.Solutions

/-!
Article: jacobi, Appendix C.1 (selected endpoint branch).
Pairing the two numerator rising factorials gives polynomials in the
actual energy, rather than in a chosen square root. This identifies the
original reference solution with a true polynomial-coefficient series
and prepares its entire energy dependence and uniform endpoint estimates.
Use: proves spectral analyticity without differentiating the arbitrary square-root branch in the reference definition.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex Polynomial
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The true reference hypergeometric coefficient expressed polynomially in the original complex energy.
Use: proves spectral analyticity without differentiating the arbitrary square-root branch in the reference definition.
Article: jacobi, Appendix C.1 (selected endpoint branch).
-/
def energyCoefficient (a : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((n.factorial:ℂ)⁻¹)*(∏ j∈Finset.range n,
    (((gamma a:ℂ)+j)^2-(z-(jacobi.Jacobi.endpointCorrection a:ℂ))/(Real.pi:ℂ)^2))*
      ((ascPochhammer ℂ n).eval ((gamma a:ℂ)+1/2))⁻¹

/-- Each original reference expansion coefficient is an entire polynomial in the genuine complex energy.
Use: the actual spectral function inherits analyticity from its normally convergent polynomial-coefficient series.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: each finite product factor is affine in energy, and both normalization inverses are energy-independent constants. -/
theorem energyCoefficient_analytic (a : ℝ) (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (energyCoefficient a n) z := by
  unfold energyCoefficient
  fun_prop

/-- The paired original frequency numerator product is exactly the finite polynomial product in its true energy square.
Use: identifies the genuine hypergeometric reference definition with the polynomial-coefficient spectral series.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: both finite products start at one. Each next paired factor is
(gamma+n)^2-omega^2/pi^2, and the prescribed true square replaces
omega^2 by the original shifted energy. -/
theorem paired_pochhammer (a : ℝ) {omega z : ℂ}
    (h : omega^2=z-(jacobi.Jacobi.endpointCorrection a:ℂ)) (n : ℕ) :
    (ascPochhammer ℂ n).eval ((gamma a:ℂ)-omega/(Real.pi:ℂ))*
      (ascPochhammer ℂ n).eval ((gamma a:ℂ)+omega/(Real.pi:ℂ))=
      ∏ j∈Finset.range n,(((gamma a:ℂ)+j)^2-
        (z-(jacobi.Jacobi.endpointCorrection a:ℂ))/(Real.pi:ℂ)^2) := by
  -- This is a finite identity before any infinite series or analyticity argument.
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval,ascPochhammer_succ_eval,Finset.prod_range_succ]
    calc
      _ = ((ascPochhammer ℂ n).eval ((gamma a:ℂ)-omega/(Real.pi:ℂ))*
        (ascPochhammer ℂ n).eval ((gamma a:ℂ)+omega/(Real.pi:ℂ)))*
        (((gamma a:ℂ)+n)^2-omega^2/(Real.pi:ℂ)^2) := by ring
      _ = _ := by rw [ih,h]

/-- The true energy coefficients equal the original frequency coefficients for every frequency with the prescribed energy square.
Use: replaces a chosen frequency root by entire polynomials in the actual original energy.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: substitute the proved finite paired-rising-factorial identity into the literal community coefficient formula. -/
theorem energyCoefficient_eq_frequency (a : ℝ) {omega z : ℂ}
    (h : omega^2=z-(jacobi.Jacobi.endpointCorrection a:ℂ)) (n : ℕ) :
    energyCoefficient a n z=frequencyCoefficient a n omega := by
  unfold energyCoefficient frequencyCoefficient ordinaryHypergeometricCoefficient
  rw [← paired_pochhammer a h n]
  ring

/-- The original arbitrary-energy reference function is exactly its genuine polynomial-coefficient spectral series.
Use: proves entire energy dependence and local uniform endpoint estimates for the actual source reference solution.
Article: jacobi, Lemma C.1.
Proof: expand the actual community hypergeometric definition at its true frequency root and replace every coefficient by the proved energy polynomial. -/
theorem solution_eq_energy_series (a : ℝ) (z : ℂ) (t : ℝ) :
    solution a z t=(weight a t:ℂ)*
      ∑' n,energyCoefficient a n z*(coordinate t:ℂ)^n := by
  -- The two sums are termwise identical actual definitions, even before restricting the spatial convergence disk.
  unfold solution wave waveCore
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  congr 1
  apply tsum_congr
  intro n
  rw [energyCoefficient_eq_frequency a (frequency_square _) n]
  rfl

end
end jacobi.Reference
