import krylov.Design.FiniteAtomicRepresentation

/-!
Article: main_krylov, apC:lem:natoms, prescribed support size and exact supremum.
Use: identify the full compact-measure optimum with the supremum over genuine
spectral probability measures having exactly any prescribed N >= M+1 atoms.
Source: the article's positive-mass padding argument, after the independently
proved sharp atomic-optimizer theorem and actual finite-measure realization.
-/

/-!
Article: krylov, Lemma D.4 [apC:lem:natoms].

Constructive padding by distinct atoms approximates the all-measure optimum at each prescribed
N≥M+1, proving equality of actual suprema.
This is a supremum statement for exactly N atoms; it does not claim that an N-atomic maximizer
always exists.
-/

namespace krylov.Design
noncomputable section
open MeasureTheory Set jacobi.Finite
open scoped BigOperators

/-- Genuine distinct positive N-atom designs on the original physical interval.
Article: main_krylov, apC:lem:natoms. -/
def AtomicIntervalDesign (I : chebyshev1.SpectralInterval) (N : ℕ) :=
  {M : DiscreteMeasure N // ∀ i, M.node i ∈ Icc I.mu I.L}

/-- The original mixed objective evaluated at the actual finite spectral probability measure.
Article: main_krylov, apC:lem:natoms. -/
def atomicDesignObjective (I : chebyshev1.SpectralInterval) (D : ℕ) (w : Fin D → ℝ) (γ : ℝ)
    {N : ℕ} (M : AtomicIntervalDesign I N) : ℝ :=
  intervalObjective I D w γ (atomicProbability M.val
    (fun i => ⟨M.val.node i, M.property i⟩ : Fin N → Spectrum I))

/-- The exact full-measure optimum, defined as the actual real supremum.
Article: main_krylov, thm:B and apC:lem:natoms, Gamma*. -/
def optimalValue (I : chebyshev1.SpectralInterval) (D : ℕ) (w : Fin D → ℝ) (γ : ℝ) : ℝ :=
  sSup (Set.range (intervalObjective I D w γ))

/-- The exact supremum when the spectral measure must have precisely N distinct positive atoms.
Article: main_krylov, apC:lem:natoms. -/
def atomicDesignValue (I : chebyshev1.SpectralInterval) (N D : ℕ) (w : Fin D → ℝ) (γ : ℝ) : ℝ :=
  sSup (Set.range (atomicDesignObjective I D w γ (N := N)))

/-- A genuine maximizing measure realizes the actual real supremum.
Article: main_krylov, thm:B. -/
theorem optimalValue_eq_of_maximizer (I : chebyshev1.SpectralInterval) (D : ℕ)
    (w : Fin D → ℝ) (γ : ℝ) (ν : ProbabilityMeasure (Spectrum I))
    (hopt : ∀ η, intervalObjective I D w γ η ≤ intervalObjective I D w γ ν) :
    optimalValue I D w γ = intervalObjective I D w γ ν := by
  have hne : (Set.range (intervalObjective I D w γ)).Nonempty := ⟨_, ν, rfl⟩
  have hbd : BddAbove (Set.range (intervalObjective I D w γ)) := by
    refine ⟨intervalObjective I D w γ ν, ?_⟩
    rintro _ ⟨η, rfl⟩
    exact hopt η
  exact le_antisymm (csSup_le hne (by rintro _ ⟨η, rfl⟩; exact hopt η))
    (le_csSup hbd ⟨ν, rfl⟩)

/-- The full-measure optimum is approximated arbitrarily well by actual exactly-N spectral designs.
Article: main_krylov, apC:lem:natoms, quantitative cofinality.
Proof: attain the true maximum with at most M+1 support points, recover its
actual finite spectral weights, then add the required distinct positive atoms. -/
theorem exists_prescribed_atoms_near_optimal (I : chebyshev1.SpectralInterval) (D N : ℕ)
    (hN : D + 1 ≤ N) (w : Fin D → ℝ) (hw : ∀ i, 0 ≤ w i)
    {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) (j : Fin D) (hj : 0 < w j)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : AtomicIntervalDesign I N, optimalValue I D w γ - ε < atomicDesignObjective I D w γ Q := by
  obtain ⟨ν, hopt, hf, hc⟩ := intervalObjective_attains_small_support I D w hw hγ₀ hγ₁ j hj
  obtain ⟨K, M, hM, hK, heq⟩ := finite_support_atomic_representation I ν hf
  have hKN : K ≤ N := hK.trans (hc.trans hN)
  obtain ⟨Q, hQ, happrox⟩ := exists_exact_atoms_approximation I M hM hKN D w hw hγ₀.le hγ₁ hε
  refine ⟨⟨Q, hQ⟩, ?_⟩
  rw [optimalValue_eq_of_maximizer I D w γ ν hopt, heq]
  exact happrox

/-- The exact-N-atom supremum equals the full mixed-design optimum for every N >= M+1.
Article: main_krylov, apC:lem:natoms, the complete stated equality.
Proof: actual finite designs are genuine probability measures for one inequality;
the proved arbitrary-tolerance exact-atom approximation gives the reverse inequality. -/
theorem atomicDesignValue_eq_optimalValue (I : chebyshev1.SpectralInterval) (D N : ℕ)
    (hN : D + 1 ≤ N) (w : Fin D → ℝ) (hw : ∀ i, 0 ≤ w i)
    {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) (j : Fin D) (hj : 0 < w j) :
    atomicDesignValue I N D w γ = optimalValue I D w γ := by
  obtain ⟨ν, hopt⟩ := intervalObjective_attains I D w hw hγ₀.le
  have hval := optimalValue_eq_of_maximizer I D w γ ν hopt
  have hupper (Q : AtomicIntervalDesign I N) : atomicDesignObjective I D w γ Q ≤ optimalValue I D w γ := by
    rw [hval]
    exact hopt _
  have hbd : BddAbove (Set.range (atomicDesignObjective I D w γ (N := N))) := by
    refine ⟨optimalValue I D w γ, ?_⟩
    rintro _ ⟨Q, rfl⟩
    exact hupper Q
  obtain ⟨Q₀, _⟩ := exists_prescribed_atoms_near_optimal I D N hN w hw hγ₀ hγ₁ j hj
    (by norm_num : (0 : ℝ) < 1)
  have hne : (Set.range (atomicDesignObjective I D w γ (N := N))).Nonempty := ⟨_, Q₀, rfl⟩
  apply le_antisymm (csSup_le hne (by rintro _ ⟨Q, rfl⟩; exact hupper Q))
  by_contra hn
  have hlt : atomicDesignValue I N D w γ < optimalValue I D w γ := lt_of_not_ge hn
  let ε := (optimalValue I D w γ - atomicDesignValue I N D w γ) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨Q, hQ⟩ := exists_prescribed_atoms_near_optimal I D N hN w hw hγ₀ hγ₁ j hj hε
  have hs : atomicDesignObjective I D w γ Q ≤ atomicDesignValue I N D w γ :=
    le_csSup hbd ⟨Q, rfl⟩
  dsimp [ε] at hQ
  linarith

end
end krylov.Design
