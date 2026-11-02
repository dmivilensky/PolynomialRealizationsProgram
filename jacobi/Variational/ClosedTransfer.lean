import jacobi.Finite.ClosedSpectrum
import jacobi.Packing.ArbitrarySequence
import jacobi.Variational.Transfer

/-!
Continuum lower bounds for the entire closed polynomial fibre.
Every candidate is approximated by an actual contractive Jacobi matrix
with vanishing normalized energy error and full spectral l1 error.
The all-block packing and proved continuum compactness then transfer the
actual infimum, allowing arbitrary restarts and repeated roots at minus one.
Use: AllThreeTerm applies the result to the padded Nesterov polynomial.
Article: jacobi, Lemma 5.2 and Theorem 3.2.
Article role: packing and spectral transfer along arbitrary cofinal dimension sequences.
-/
namespace jacobi.Variational
noncomputable section
open chebyshev1 chebyshev2 chebyshev2.Continuum
open jacobi.Finite jacobi.Packing Set Real Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The true normalized infimum over all nonnegative-link realizations
of the prescribed polynomial, without an irreducibility restriction.
Article: jacobi, Lemma 5.2 and Theorem 3.2.
-/
def closedFibreEnergyInfimum {N : ℕ} (S : ClosedNodes N) : ℝ≥0∞ :=
  sInf (fibreCost '' {J : Jacobi N | InClosedFiber J S.polynomial})

/-- Closed fibres are nonempty even when all roots coincide. Their
normalized energy infimum is therefore finite in each fixed dimension.
Article: jacobi, Lemma 5.2 and Theorem 3.2.
-/
theorem closedFibreEnergyInfimum_ne_top {N : ℕ} (S : ClosedNodes N) :
    closedFibreEnergyInfimum S≠∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (sInf_le ⟨S.diagonalChain,S.diagonalChain_mem,rfl⟩)

/-- Actual approximating matrices retain both the normalized energy
limit and the complete target edge spectrum. The shrinking construction
supplies every witness and every vanishing error, also for zero links.
Article: jacobi, Lemma 5.2 and Theorem 3.2.
-/
theorem closed_sequence_approximation (N : ℕ → ℕ) (S : ∀ n,ClosedNodes (N n))
    (hN : ∀ n,0<N n) (J : ∀ n,Jacobi (N n))
    (hJ : ∀ n,InClosedFiber (J n) (S n).polynomial) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (closedFibreSpectrum (S n)) Λ.value) atTop (𝓝 0)) :
    ∃ K : ∀ n,Jacobi (N n),∃ hc : ∀ n,opNorm (K n).matrix<1,
      Tendsto (fun n => ((K n).energy-(J n).energy)/(N n:ℝ)^3) atTop (𝓝 0) ∧
      Tendsto (fun n => distance (finiteEigenvalue (K n) (hc n)) Λ.value) atTop (𝓝 0) := by
  choose K hc he hs using fun n => (S n).exists_spectral_approximation (hJ n)
    (d := 1/((n:ℝ)+1)) (by positivity)
  have hδ : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have herr : Tendsto (fun n => distance (finiteEigenvalue (K n) (hc n))
      (closedFibreSpectrum (S n))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => tsum_nonneg (fun _ => abs_nonneg _)) _ hδ
    intro n
    simpa only [(S n).closedSpectrum_eq (hJ n)] using (hs n).le
  refine ⟨K,hc,?_,?_⟩
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hδ
    intro n
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (show 0<(N n:ℝ)^3 from pow_pos (Nat.cast_pos.mpr (hN n)) 3)]
    have hn : (1:ℝ)≤(N n:ℝ)^3 := one_le_pow₀ (by exact_mod_cast (show 1≤N n from hN n))
    exact (div_le_self (abs_nonneg _) hn).trans (he n).le
  · have ht := herr.add hd
    simp only [zero_add] at ht
    apply squeeze_zero (fun _ => tsum_nonneg (fun _ => abs_nonneg _)) _ ht
    intro n
    exact spectral_distance_triangle
      (matrixSpectralData _ (normalizedGreen_positive (K n) (hc n))).eigenvalue_summable
      (matrixSpectralData _ (normalizedGreen_posSemidef_of_posDef
        ((S n).endpoint_posDef (S n).diagonalChain_mem))).eigenvalue_summable Λ.summable

/-- Every actual closed-fibre sequence with convergent normalized energy
satisfies all root-normalized continuum lower bounds. Only the prescribed
edge convergence is an input; the approximants and densities are constructed.
Article: jacobi, Lemma 5.2 and Theorem 3.2.
-/
theorem closed_sequence_transfer (N : ℕ → ℕ) (S : ∀ n,ClosedNodes (N n))
    (hN : ∀ n,0<N n) (hNlim : Tendsto N atTop atTop)
    (J : ∀ n,Jacobi (N n)) (hJ : ∀ n,InClosedFiber (J n) (S n).polynomial)
    (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (closedFibreSpectrum (S n)) Λ.value) atTop (𝓝 0))
    {C : ℝ} (hE : Tendsto (fun n => (J n).energy/(N n:ℝ)^3) atTop (𝓝 C)) :
    (∀ A : Set Observation,rootInfimum A Λ.mass (threshold Λ)≤ENNReal.ofReal C) ∧
      ∀ s : ℝ,0≤s → rootFredholmInfimum s Λ.mass (Λ.fredholm s)≤ENNReal.ofReal C := by
  obtain ⟨K,hc,he,hs⟩ := closed_sequence_approximation N S hN J hJ Λ hd
  have ht := he.add hE
  simp only [zero_add,sub_div,sub_add_cancel] at ht
  exact arbitrary_sequence_transfer N K hc hN hNlim Λ hs ht

/-- Full transfer from the actual closed-fibre infima. Near-minimizers
come from the whole fibre; no minimizing sequence, limiting density,
simple roots or positive links are assumed. The infinite lower-limit
case and arbitrary cofinal dimensions are included.
Article: jacobi, Lemma 5.2 and Theorem 3.2.
-/
theorem closed_fibre_transfer (N : ℕ → ℕ) (S : ∀ n,ClosedNodes (N n))
    (hN : ∀ n,0<N n) (hNlim : Tendsto N atTop atTop) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (closedFibreSpectrum (S n)) Λ.value) atTop (𝓝 0)) :
    (∀ A : Set Observation,rootInfimum A Λ.mass (threshold Λ)≤
      liminf (fun n => closedFibreEnergyInfimum (S n)) atTop) ∧
      ∀ s : ℝ,0≤s → rootFredholmInfimum s Λ.mass (Λ.fredholm s)≤
        liminf (fun n => closedFibreEnergyInfimum (S n)) atTop := by
  by_cases hL : liminf (fun n => closedFibreEnergyInfimum (S n)) atTop=∞
  · simp only [hL,le_top,implies_true,and_self]
  obtain ⟨α,hα,J,hJ,hcost⟩ := exists_liminf_competitors (X := fun n => Jacobi (N n))
    (fun _ => fibreCost) (fun n => {J | InClosedFiber J (S n).polynomial}) hL
  have ht := (ENNReal.tendsto_toReal hL).comp hcost
  have hnonneg n : 0≤(J n).energy/(N (α n):ℝ)^3 :=
    div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
  simp only [fibreCost,Function.comp_def,ENNReal.toReal_ofReal (hnonneg _)] at ht
  have h := closed_sequence_transfer (fun n => N (α n)) (fun n => S (α n))
    (fun n => hN (α n)) (hNlim.comp hα) J hJ Λ (hd.comp hα) ht
  simpa only [ENNReal.ofReal_toReal hL] using h

/-- Dropping the root constraint gives all the printed moment and
Fredholm lower bounds for the same closed-fibre lower limit.
Article: jacobi, Lemma 5.2 and Theorem 3.2.
-/
theorem closed_fibre_transfer_relaxed (N : ℕ → ℕ) (S : ∀ n,ClosedNodes (N n))
    (hN : ∀ n,0<N n) (hNlim : Tendsto N atTop atTop) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (closedFibreSpectrum (S n)) Λ.value) atTop (𝓝 0)) :
    (∀ A : Set Observation,relaxedInfimum A Λ.mass (threshold Λ)≤
      liminf (fun n => closedFibreEnergyInfimum (S n)) atTop) ∧
      ∀ s : ℝ,0≤s → fredholmInfimum s Λ.mass (Λ.fredholm s)≤
        liminf (fun n => closedFibreEnergyInfimum (S n)) atTop := by
  obtain ⟨hA,hF⟩ := closed_fibre_transfer N S hN hNlim Λ hd
  exact ⟨fun A => (relaxed_le_root A Λ.mass (threshold Λ)).trans (hA A),
    fun s hs => (fredholm_le_root s Λ.mass (Λ.fredholm s)).trans (hF s hs)⟩

end
end jacobi.Variational
