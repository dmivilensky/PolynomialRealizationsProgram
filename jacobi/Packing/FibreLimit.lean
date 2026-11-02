import jacobi.Packing.FibreSpectrum
import jacobi.Variational.EdgeLimit

/-!
Article: jacobi, Theorem D.4.
The common finite-fibre scaled trace converges to the edge mass and the
printed error 4sqrt(mu_N/N) tends to zero. Thus every sequence of actual
fibre members gives packed density spectra converging to that edge in l1.
The estimates are uniform over the complete fibres and do not assume a
finite energy bound or existence of a finite-dimensional minimizer.
Source: proved packing error, exact finite spectral identification and l1 trace stability.
Use: all actual fibre members obey the same finite-to-continuum l1 bound.
-/
namespace jacobi.Packing
noncomputable section
open chebyshev1 chebyshev2 chebyshev2.Continuum
open jacobi.Finite jacobi.Variational MeasureTheory Real Set Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The printed uniform packing error relative to an arbitrary limiting edge spectrum.
Use: all actual fibre members obey the same finite-to-continuum l1 bound.
Article: jacobi, Theorem D.4.
-/
def fibreTransferError {N : ℕ} (S : Nodes N) (Λ : EdgeSpectrum) : ℝ :=
  4*sqrt ((∑' j, fibreSpectrum S j)/(N : ℝ))+distance (fibreSpectrum S) Λ.value

/-- The actual packed spectrum is within the printed uniform error of the limiting edge spectrum.
Use: transfers arbitrary near-minimizing fibre matrices rather than a specially chosen finite realization.
Article: jacobi, Theorem D.4.
Proof: combine the proved packing comparison with the l1 triangle inequality;
the finite resolvent spectrum and trace are the same for every fibre member. -/
theorem packed_fibre_edge_bound {N : ℕ} (S : Nodes N) (hN : 0 < N) (Λ : EdgeSpectrum)
    (J : Jacobi N) (hJ : InFiber J S.polynomial) :
    distance (variationalDensity J (S.contractive hJ) hN).spectrum Λ.value ≤ fibreTransferError S Λ := by
  -- Identify both spectra and the mass with their actual fibre formulas before applying the triangle estimate.
  let m := variationalDensity J (S.contractive hJ) hN
  have hp := spectral_distance J (S.contractive hJ) hN
  rw [finiteEigenvalue_eq_fibreSpectrum S hN J hJ,mass_eq_fibreSpectrum S hN J hJ] at hp
  have ht := spectral_distance_triangle
    (chebyshev2.Continuum.kernelSpectralData m.integrable m.nonneg).eigenvalue_summable
    (fibreSpectrum_summable S hN) Λ.summable
  change distance m.spectrum (fibreSpectrum S) ≤ 4*sqrt ((∑' j, fibreSpectrum S j)/(N : ℝ)) at hp
  change distance m.spectrum Λ.value ≤
    distance m.spectrum (fibreSpectrum S)+distance (fibreSpectrum S) Λ.value at ht
  exact ht.trans (add_le_add hp (le_refl _))

/-- Convergence of the padded finite spectra fixes the common fibre mass limit.
Use: the trace-dependent packing error vanishes even when the edge mass is not one.
Article: jacobi, Theorem D.4.
Proof: the absolute difference of the two spectral sums is bounded by their l1 distance. -/
theorem fibre_mass_limit (N : ℕ → ℕ) (S : ∀ n, Nodes (N n)) (hN : ∀ n, 0 < N n)
    (Λ : EdgeSpectrum) (hd : Tendsto (fun n => distance (fibreSpectrum (S n)) Λ.value) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' j, fibreSpectrum (S n) j) atTop (𝓝 Λ.mass) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hd
  intro n
  exact mass_distance (fibreSpectrum_summable (S n) (hN n)) Λ.summable

/-- The uniform printed fibre packing error tends to zero along every cofinal dimension sequence.
Use: transfers lower bounds uniformly over complete arbitrary-polynomial fibres.
Article: jacobi, Theorem D.4.
Proof: l1 spectral convergence gives finite mass convergence; reciprocal
dimension tends to zero, so mu_N/N and its square root tend to zero. -/
theorem fibreTransferError_limit (N : ℕ → ℕ) (S : ∀ n, Nodes (N n)) (hN : ∀ n, 0 < N n)
    (hNlim : Tendsto N atTop atTop) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (fibreSpectrum (S n)) Λ.value) atTop (𝓝 0)) :
    Tendsto (fun n => fibreTransferError (S n) Λ) atTop (𝓝 0) := by
  -- There is no normalization to mass one in either the trace limit or the packing error.
  have hm := fibre_mass_limit N S hN Λ hd
  have hi : Tendsto (fun n => 1/(N n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hNlim
  have hdiv := hm.mul hi
  simp only [mul_zero,mul_one_div] at hdiv
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hdiv
  simp only [Real.sqrt_zero] at hs
  have ht := (hs.const_mul 4).add hd
  change Tendsto (fun n => 4*sqrt ((∑' j, fibreSpectrum (S n) j)/(N n : ℝ))+
    distance (fibreSpectrum (S n)) Λ.value) atTop (𝓝 0)
  simpa only [Function.comp_def,mul_zero,zero_add] using ht

/-- Every sequence of actual finite-fibre matrices has packed spectra converging to the prescribed limiting edge.
Use: applies continuum Transfer to the actual finite near-minimizers selected from the whole fibre.
Article: jacobi, Theorem D.4.
Proof: squeeze the actual nonnegative spectral l1 errors by the proved common vanishing fibre error. -/
theorem packed_fibre_edge_limit (N : ℕ → ℕ) (S : ∀ n, Nodes (N n)) (hN : ∀ n, 0 < N n)
    (hNlim : Tendsto N atTop atTop) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (fibreSpectrum (S n)) Λ.value) atTop (𝓝 0))
    (J : ∀ n, Jacobi (N n)) (hJ : ∀ n, InFiber (J n) (S n).polynomial) :
    Tendsto (fun n => distance (variationalDensity (J n) ((S n).contractive (hJ n)) (hN n)).spectrum Λ.value)
      atTop (𝓝 0) := by
  exact squeeze_zero (fun _ => tsum_nonneg (fun _ => abs_nonneg _))
    (fun n => packed_fibre_edge_bound (S n) (hN n) Λ (J n) (hJ n))
    (fibreTransferError_limit N S hN hNlim Λ hd)

end
end jacobi.Packing
