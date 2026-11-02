import jacobi.Finite.MatrixSpectrumContinuity
import jacobi.Packing.VariationalDensity
import jacobi.Variational.EdgeLimit

/-!
Packing and continuum transfer for arbitrary strictly contractive chains.
The construction already handles all blocks. No simple-node description
or irreducibility premise is needed for its spectral error or energy limit.
Use: ClosedTransfer applies this theorem to the actual approximants of
closed-fibre matrices, including repeated roots at minus one.
Article: jacobi, Lemma 5.2 and Theorem 3.2.
Article role: packing and spectral transfer along arbitrary cofinal dimension sequences.
-/
namespace jacobi.Packing
noncomputable section
open chebyshev1 chebyshev2 chebyshev2.Continuum jacobi.Finite
open jacobi.Variational Filter Real Set
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The full actual normalized Green spectrum has the same sum as the
mass of the packing. This identity does not use a simple node list.
Article: jacobi, Lemma 5.2 and Theorem 3.2.
-/
theorem finiteEigenvalue_mass {N : ℕ} (J : Jacobi N) (hc : opNorm J.matrix<1) :
    (∑' j,finiteEigenvalue J hc j)=mass J := by
  rw [finiteEigenvalue,matrixSpectrum_tsum_trace,Jacobi.normalizedGreen,Matrix.trace_smul]
  simp only [mass,smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- Full spectral l1 convergence determines the actual packing masses
for arbitrary chains, including every reducible chain.
Article: jacobi, Lemma 5.2 and Theorem 3.2.
-/
theorem arbitrary_mass_limit (N : ℕ → ℕ) (J : ∀ n,Jacobi (N n))
    (hc : ∀ n,opNorm (J n).matrix<1) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (finiteEigenvalue (J n) (hc n)) Λ.value) atTop (𝓝 0)) :
    Tendsto (fun n => mass (J n)) atTop (𝓝 Λ.mass) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hd
  intro n
  rw [← finiteEigenvalue_mass (J n) (hc n),Real.norm_eq_abs]
  exact mass_distance (matrixSpectralData _ (normalizedGreen_positive (J n) (hc n))).eigenvalue_summable
    Λ.summable

/-- The actual packed density spectra converge to the prescribed edge
for every cofinal strictly contractive sequence.
Article: jacobi, Lemma 5.2 and Theorem 3.2.
-/
theorem arbitrary_packed_edge_limit (N : ℕ → ℕ) (J : ∀ n,Jacobi (N n))
    (hc : ∀ n,opNorm (J n).matrix<1) (hN : ∀ n,0<N n)
    (hNlim : Tendsto N atTop atTop) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (finiteEigenvalue (J n) (hc n)) Λ.value) atTop (𝓝 0)) :
    Tendsto (fun n => distance (variationalDensity (J n) (hc n) (hN n)).spectrum Λ.value)
      atTop (𝓝 0) := by
  have hm := arbitrary_mass_limit N J hc Λ hd
  have hi : Tendsto (fun n => 1/(N n:ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hNlim
  have hdiv := hm.mul hi
  simp only [mul_zero,mul_one_div] at hdiv
  have hs := hdiv.sqrt
  simp only [sqrt_zero] at hs
  have he := (hs.const_mul 4).add hd
  simp only [mul_zero,zero_add] at he
  apply squeeze_zero (fun _ => tsum_nonneg (fun _ => abs_nonneg _)) _ he
  intro n
  have h := spectral_distance_triangle
    (kernelSpectralData (variationalDensity (J n) (hc n) (hN n)).integrable
      (variationalDensity (J n) (hc n) (hN n)).nonneg).eigenvalue_summable
    (matrixSpectralData _ (normalizedGreen_positive (J n) (hc n))).eigenvalue_summable Λ.summable
  exact h.trans (add_le_add (spectral_distance (J n) (hc n) (hN n)) (le_refl _))

/-- Continuum lower bounds apply to the true normalized energy limit
of an arbitrary strictly contractive chain sequence. No candidate density
or minimizing witness is assumed; packing and transfer construct it.
Article: jacobi, Lemma 5.2 and Theorem 3.2.
-/
theorem arbitrary_sequence_transfer (N : ℕ → ℕ) (J : ∀ n,Jacobi (N n))
    (hc : ∀ n,opNorm (J n).matrix<1) (hN : ∀ n,0<N n)
    (hNlim : Tendsto N atTop atTop) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (finiteEigenvalue (J n) (hc n)) Λ.value) atTop (𝓝 0))
    {C : ℝ} (hE : Tendsto (fun n => (J n).energy/(N n:ℝ)^3) atTop (𝓝 C)) :
    (∀ A : Set Observation,rootInfimum A Λ.mass (threshold Λ)≤ENNReal.ofReal C) ∧
      ∀ s : ℝ,0≤s → rootFredholmInfimum s Λ.mass (Λ.fredholm s)≤ENNReal.ofReal C := by
  let m n := variationalDensity (J n) (hc n) (hN n)
  have hr n : (m n).rootMass≤1 := (variationalDensity_integrals (J n) (hc n) (hN n)).2.1.le
  have hd' := arbitrary_packed_edge_limit N J hc hN hNlim Λ hd
  have h := density_transfer m Λ hr hd'
  have hcost : Tendsto (fun n => (m n).cost) atTop (𝓝 (ENNReal.ofReal C)) := by
    have he n : (m n).cost=ENNReal.ofReal ((J n).energy/(N n:ℝ)^3) :=
      congrArg ENNReal.ofReal (variationalDensity_integrals (J n) (hc n) (hN n)).2.2
    simpa only [he,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hE
  simpa only [hcost.liminf_eq] using h

end
end jacobi.Packing
