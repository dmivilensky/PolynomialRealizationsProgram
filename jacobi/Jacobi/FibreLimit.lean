import jacobi.Bessel.EdgeData
import jacobi.Packing.FibreLimit

/-!
Article: jacobi, Lemma 1.3.
The genuine normalized Jacobi nodes and Bessel spectrum instantiate the
existing arbitrary-polynomial finite-fibre spectral and packing theorems.
No eigenvalue enumeration or tail bound is added as an assumption.
Use: all finite-fibre matrix and packing results apply to the genuine source polynomials with no second construction.
-/
namespace jacobi.Jacobi
noncomputable section
open Filter jacobi.Finite jacobi.Variational
open scoped Topology

/-- The actual normalized Jacobi spectrum is exactly the earlier arbitrary-fibre spectral sequence.
Use: all finite-fibre matrix and packing results apply to the genuine source polynomials with no second construction.
Article: jacobi, Lemma 1.3.
Proof: within the degree use the proved actual reciprocal-node identity;
beyond it both independently defined sequences are zero. -/
theorem fibreSpectrum_eq_finiteLambdaAt {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    jacobi.Packing.fibreSpectrum (nodes a b ha hb n)=finiteLambdaAt a b ha hb n := by
  -- Both definitions use the same complete, genuinely proved ordered Jacobi zero list.
  funext k
  by_cases hk : k<n
  · rw [jacobi.Packing.fibreSpectrum,dite_eq_left hk,finiteLambdaAt_eq ha hb hk,
      finiteLambda_node ha hb ⟨k,hk⟩]
    simp only [jacobi.Packing.nodeResolvent,mul_inv_rev,div_eq_mul_inv,one_mul]
  · rw [jacobi.Packing.fibreSpectrum,dite_eq_right hk,finiteLambdaAt_zero ha hb (not_lt.mp hk)]

/-- Every actual Jacobi-polynomial fibre matrix has precisely the genuine finite Jacobi resolvent spectrum.
Use: proves the matrix assertion of Lemma spec uniformly over all admissible fibre members.
Article: jacobi, Lemma 1.3.
Proof: reuse the proved arbitrary-fibre spectral theorem and the exact identification of the actual finite Jacobi sequence. -/
theorem finiteEigenvalue_eq {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n : ℕ} (hn : 0<n) (J : chebyshev2.Jacobi n)
    (hJ : InFiber J (nodes a b ha hb n).polynomial) :
    jacobi.Packing.finiteEigenvalue J ((nodes a b ha hb n).contractive hJ)=
      finiteLambdaAt a b ha hb n := by
  rw [jacobi.Packing.finiteEigenvalue_eq_fibreSpectrum _ hn J hJ,fibreSpectrum_eq_finiteLambdaAt ha hb]

/-- The genuine Jacobi fibre spectra satisfy the full spectral convergence premise of the general Transfer theorem.
Use: discharges the analytic edge hypothesis for all previously proved moment, root-mass and Fredholm lower bounds.
Article: jacobi, Lemma 1.3.
Proof: the fibre sequence is the actual padded Jacobi spectrum; apply its already proved unconditional L1 convergence. -/
theorem fibre_spectral_limit {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    Tendsto (fun n : ℕ => distance (jacobi.Packing.fibreSpectrum (nodes a b ha hb n))
      (jacobi.Bessel.edgeSpectrum a ha).value) atTop (𝓝 0) := by
  simp_rw [fibreSpectrum_eq_finiteLambdaAt ha hb]
  exact finiteLambdaAt_l1_tendsto ha hb

/-- Any sequence of actual fibre matrices has its entire scaled resolvent spectrum converging to the genuine Bessel edge spectrum.
Use: completes the matrix and beta-independence assertions of Lemma spec for arbitrary choices in the fibres.
Article: jacobi, Lemma 1.3.
Proof: each arbitrary matrix has exactly the same actual finite Jacobi
spectral sequence. Apply the already established full L1 convergence along
the cofinal positive dimensions n+1. -/
theorem arbitrary_fibre_spectral_limit {a b : ℝ} (ha : -1<a) (hb : -1<b)
    (J : ∀ n : ℕ,chebyshev2.Jacobi (n+1))
    (hJ : ∀ n,InFiber (J n) (nodes a b ha hb (n+1)).polynomial) :
    Tendsto (fun n : ℕ => ∑' k, |jacobi.Packing.finiteEigenvalue (J n)
      ((nodes a b ha hb (n+1)).contractive (hJ n)) k- jacobi.Bessel.edgeValue a ha k|)
      atTop (𝓝 0) := by
  simp_rw [finiteEigenvalue_eq ha hb (Nat.succ_pos _) _ (hJ _)]
  exact (finiteLambdaAt_l1_tendsto ha hb).comp (tendsto_add_atTop_nat 1)

end
end jacobi.Jacobi
