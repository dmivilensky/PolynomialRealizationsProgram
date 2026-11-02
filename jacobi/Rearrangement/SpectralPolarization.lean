import jacobi.Rearrangement.GraphPolarization
import jacobi.Continuum.MultipleIntegrals
import jacobi.Variational.FredholmRelaxation

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Every actual cyclic moment, the actual top eigenvalue and the extended
Fredholm functional increase under elementary polarization. The complete
Schwarz rearrangement theorem additionally needs convergence of the sequence
of polarizations; that limiting statement is not assumed or asserted here.
Source: finite graph reflection comparison and the proved trace and moment-root identities.
Use: identifies the general graph integral with the literal cyclic moment integrand.
-/
namespace jacobi.Rearrangement
noncomputable section
open MeasureTheory Real Set Filter jacobi.Variational
open scoped BigOperators Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Sources of the edges in the closed cycle on n+1 physical vertices.
Use: identifies the general graph integral with the literal cyclic moment integrand.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def cycleLeft (n : ℕ) : Fin n ⊕ Unit → Fin (n+1)
  | .inl i => i.castSucc
  | .inr _ => Fin.last n

/-- Targets of the same closed-cycle edges.
Use: the closing edge joins the last vertex back to vertex zero.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def cycleRight (n : ℕ) : Fin n ⊕ Unit → Fin (n+1)
  | .inl i => i.succ
  | .inr _ => 0

/-- The chosen graph is exactly the article's cyclic product, including the closing edge.
Use: all graph polarization bounds refer to the same integrals as the actual operator spectrum.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: split the finite product into its n consecutive edges and its single closing edge. -/
theorem cycle_graph (m : ℝ → ℝ) (n : ℕ) (z : Fin (n+1) → ℝ) :
    graphIntegrand (cycleLeft n) (cycleRight n) m z= jacobi.Continuum.cycleIntegrand m n z := by
  rw [jacobi.Continuum.cycleIntegrand_product,graphIntegrand,Fintype.prod_sum_type]
  simp only [cycleLeft,cycleRight,Fintype.prod_unique]
  ring

/-- Every actual positive integer spectral moment increases under polarization.
Use: the complete elementary moment comparison underlying symmetric rearrangement,
and recovery of the top eigenvalue and Fredholm functional from the same spectrum.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: identify the actual spectral moment with its absolutely convergent
cyclic integral, specialize the proved graph integral inequality, and identify the polarized spectrum. -/
theorem moment_polarize (m : Density) (a : ℝ) (n : ℕ) :
    (∑' j, m.spectrum j^(n+1)) ≤ ∑' j, (m.polarize a).spectrum j^(n+1) := by
  -- The trace formula and graph comparison use the same literal density, without spectral proxies.
  have h := graph_integral_polarize (cycleLeft n) (cycleRight n) m a
  simp_rw [cycle_graph] at h
  simp only [L1Source.spectrum]
  rw [jacobi.Continuum.moment_multiple_integral m.integrable m.measurable m.nonneg n,
    jacobi.Continuum.moment_multiple_integral (m.polarize a).integrable (m.polarize a).measurable
      (m.polarize a).nonneg n]
  exact h

/-- The actual largest eigenvalue increases under polarization as well.
Use: the ground-state spectral constraint is preserved together with all finite moments.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: take the positive integer roots of the proved moment inequalities and
use the already established moment-root limit for each actual positive compact spectrum. -/
theorem top_polarize (m : Density) (a : ℝ) : observe m .top ≤ observe (m.polarize a) .top := by
  -- Recover the same operator's top eigenvalue; no separate rearrangement theorem for H1 is assumed.
  have hm := jacobi.Continuum.kernel_moment_root_limit m.integrable m.nonneg
  have hp := jacobi.Continuum.kernel_moment_root_limit (m.polarize a).integrable (m.polarize a).nonneg
  apply le_of_tendsto_of_tendsto hm hp
  exact Filter.Eventually.of_forall fun n => rpow_le_rpow
    (tsum_nonneg (fun j => pow_nonneg
      ((chebyshev2.Continuum.kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg j) _))
    (moment_polarize m a n) (by positivity)

/-- Polarization increases the actual extended Fredholm functional, including at spectral poles.
Use: preserves the Fredholm constraint in the eventual symmetric rearrangement construction.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: apply the proved nonnegative Fredholm moment expansion term by term
to the actual moment inequalities; the argument remains valid for infinite values. -/
theorem fredholm_polarize (m : Density) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    m.fredholm s ≤ (m.polarize a).fredholm s := by
  apply fredholm_mono_of_moments m (m.polarize a) hs
  intro n
  simpa only [Nat.add_assoc] using moment_polarize m a (n+1)

end
end jacobi.Rearrangement
