import jacobi.Support.ComplexEdge
import jacobi.Support.EdgeEnergy
import jacobi.Support.FixedWeightLimit

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The complete original support edge proposition: arbitrary convergent
complex energies, uniform convergence over the entire physical half
chain, every fixed corrected support node and every fixed support
weight, all with the exact original Gamma and reference normalizations.
Use: naturalWave_complex_edge writes its actual polynomial limit in the source's f normalization, so fixed-edge Gram products cancel precisely the same original weight amplitude.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The normalized Volterra limit has exactly the original printed reference-solution amplitude.
Use: naturalWave_complex_edge writes its actual polynomial limit in the source's f normalization, so fixed-edge Gram products cancel precisely the same original weight amplitude.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the genuine reference solution is its actual sine-power weight times its regular core. The actual top profile is its positive Gamma amplitude times that same weight; the printed kappa_U definition supplies exactly the reciprocal pi power. -/
theorem topProfile_regularWave (a b:ℝ) (E:ℂ) {t:ℝ} (ht:t∈Icc (0:ℝ) 1) :
    (topProfile a b t:ℂ)*regularWave a E t=
      (topConstant a b:ℂ)*((π^gamma a:ℝ):ℂ)*solution a E t := by
  rw [solution_regularWave]
  have hs : 0≤sin (π*t) := sin_nonneg_of_nonneg_of_le_pi
    (mul_nonneg pi_pos.le ht.1) (by nlinarith [ht.2,pi_pos])
  dsimp only [topProfile,topConstant,weight]
  rw [Real.div_rpow hs pi_pos.le]
  push_cast
  field_simp [(rpow_pos_of_pos pi_pos (gamma a)).ne']

/-- The actual finite support polynomials have the full original uniform half-chain complex edge limit at every convergent printed energy sequence.
Use: the actual two-edge Gram limit evaluates these same support polynomials at target and support nodes, and then the original Gram–Cholesky construction gives the persymmetric eigenvector limits of Theorems A–B and Theorem 2.1.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the printed complex energies give the proved exact ground-scaled displacement limit. Apply the genuine uniform finite Volterra limit and rewrite the identified reference factor with the exact original amplitude. Every half-mesh point is in the original closed continuum interval, including zero. -/
theorem naturalWave_complex_edge {a b:ℝ} (ha:-1<a) (hb:-1<b) {z:ℕ→ℂ} {E:ℂ}
    (hz:Tendsto z atTop (𝓝 E)) :
    ∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀m:ℕ,2*m≤n+1→
      ‖(((n:ℝ)^(-gamma a):ℝ):ℂ)*naturalWave a b ha hb n m
          (1-z n/(2*(jacobi.Jacobi.frequency a b (n+1):ℂ)^2))-
        (topConstant a b:ℂ)*((π^gamma a:ℝ):ℂ)*
          solution a (E+(jacobi.Jacobi.endpointCorrection a:ℂ)) ((m:ℝ)/(n:ℝ))‖<ε := by
  -- The hypotheses are exactly the original parameter range and the original complex energy convergence.
  have h := naturalWave_edge ha hb (E+(jacobi.Jacobi.endpointCorrection a:ℂ))
    (fun n => 1-z n/(2*(jacobi.Jacobi.frequency a b (n+1):ℂ)^2)) (edgeEnergy_limit ha hb hz)
  intro ε hε
  obtain ⟨N,hN⟩ := h ε hε
  refine ⟨max N 1,?_⟩
  intro n hn m hm
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ht : (m:ℝ)/(n:ℝ)∈Icc (0:ℝ) 1 := by
    refine ⟨by positivity,?_⟩
    apply (div_le_iff₀ hnpos).mpr
    have : (m:ℝ)≤n := by exact_mod_cast (show m≤n by omega)
    linarith
  simpa only [topProfile_regularWave a b _ ht] using hN n (by omega) m hm

end
end jacobi.Support
