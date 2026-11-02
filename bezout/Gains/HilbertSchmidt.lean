import bezout.Gains.Matrix

/-!
Article: bezout, Theorem 4.1, both Hilbert--Schmidt perturbation classes.
Use: sharp bounds quantify every dimension and the derivative of the
actual physical oracle execution. Symmetry is an optional restriction on
the perturbations, with the same temporal Hilbert--Schmidt budget.
Proof: spectral calculus for the upper bound; explicit two-dimensional
diagonal and symmetric off-diagonal witnesses for the lower bound.
-/

namespace bezout.Gains
noncomputable section
open Polynomial chebyshev1
open scoped BigOperators Matrix
variable {N : ℕ}

/-- A nonnegative dimension-uniform Hilbert--Schmidt response coefficient.
When `symmetric=true`, each perturbation must be symmetric. -/
def HsBound (h : bezout.History N) (I : SpectralInterval) (symmetric : Bool) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (d : Type) [Fintype d] [DecidableEq d] (H : Matrix d d ℝ),
    H.IsHermitian → spectrum ℝ H ⊆ Set.Icc I.mu I.L →
    ∀ D : Fin N → Matrix d d ℝ,
      (symmetric = true → ∀ s, (D s).IsHermitian) →
      hsNorm (h.matrixResponse H D) ≤ C * Real.sqrt (∑ s, hsNorm (D s) ^ 2)

/-- The universal Hilbert--Schmidt gain for the specified perturbation class. -/
def hsGain (h : bezout.History N) (I : SpectralInterval) (symmetric : Bool := false) : ℝ :=
  sInf {C : ℝ | HsBound h I symmetric C}

/-- The physical spectral gain bounds either Hilbert--Schmidt perturbation class. -/
theorem hsBound_spectralGain (h : bezout.History N) (I : SpectralInterval)
    (symmetric : Bool) : HsBound h I symmetric (h.spectralGain I) := by
  refine ⟨h.realization.gain_nonneg I N, ?_⟩
  intro d _ _ H hH hs D _
  exact h.hs_matrixResponse_bound I H hH hs D

/-- A finite physical Hilbert--Schmidt gain exists for either perturbation class. -/
theorem hsBounds_nonempty (h : bezout.History N) (I : SpectralInterval) (symmetric : Bool) :
    {C : ℝ | HsBound h I symmetric C}.Nonempty := ⟨_, hsBound_spectralGain h I symmetric⟩

/-- Restricting perturbations to symmetric matrices preserves the spectral upper bound. -/
theorem hsGain_le_spectralGain (h : bezout.History N) (I : SpectralInterval)
    (symmetric : Bool) : hsGain h I symmetric ≤ h.spectralGain I :=
  csInf_le ⟨0, fun _ hb => hb.1⟩ (hsBound_spectralGain h I symmetric)

/-- A nonnegative quadratic energy is bounded by `C^2` whenever its own
aligned input gives `energy ≤ C*sqrt energy`. -/
theorem energy_le_sq_of_aligned {e C : ℝ} (he : 0 ≤ e) (hC : 0 ≤ C)
    (hb : e ≤ C * Real.sqrt e) : e ≤ C ^ 2 := by
  have hs := Real.sq_sqrt he
  have hn := Real.sqrt_nonneg e
  by_cases hz : Real.sqrt e = 0
  · nlinarith [sq_nonneg C]
  · have hp : 0 < Real.sqrt e := lt_of_le_of_ne hn (Ne.symm hz)
    have hl : Real.sqrt e ≤ C := by nlinarith
    nlinarith

/-- A two-dimensional diagonal Hessian is admissible whenever its two entries are. -/
theorem diagonal_pair_admissible (I : SpectralInterval) (x y : ℝ)
    (hx : x ∈ Set.Icc I.mu I.L) (hy : y ∈ Set.Icc I.mu I.L) :
    (Matrix.diagonal ![x, y]).IsHermitian ∧
      spectrum ℝ (Matrix.diagonal ![x, y]) ⊆ Set.Icc I.mu I.L := by
  refine ⟨by simp [Matrix.IsHermitian], ?_⟩
  rw [spectrum_diagonal]
  rintro z ⟨i, rfl⟩
  fin_cases i
  · exact hx
  · exact hy

/-- Arbitrary linear perturbations attain each physical spectral-pair norm. -/
theorem hsBound_kernel_lower (h : bezout.History N) (I : SpectralInterval)
    (C : ℝ) (hb : HsBound h I false C) (x y : ℝ)
    (hx : x ∈ Set.Icc I.mu I.L) (hy : y ∈ Set.Icc I.mu I.L) :
    Real.sqrt (Lower.physicalKernelSq h x y) ≤ C := by
  let a : Fin N → ℝ := fun s => Lower.physicalKernel h s x y
  let D : Fin N → Matrix (Fin 2) (Fin 2) ℝ := fun s => spectralWitness (a s)
  have had := diagonal_pair_admissible I x y hx hy
  have hu := hb.2 (Fin 2) (Matrix.diagonal ![x, y]) had.1 had.2 D (by simp)
  have hout : h.matrixResponse (Matrix.diagonal ![x, y]) D = spectralWitness (∑ s, a s ^ 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bezout.History.diagonal_matrixResponse_entry, D, spectralWitness, a, pow_two]
  have hin : ∑ s, hsNorm (D s) ^ 2 = ∑ s, a s ^ 2 := by
    simp only [D, hsNorm_spectralWitness, sq_abs]
  rw [hout, hin, hsNorm_spectralWitness,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hu
  have he := energy_le_sq_of_aligned (Finset.sum_nonneg fun _ _ => sq_nonneg _) hb.1 hu
  exact (Real.sqrt_le_iff).mpr ⟨hb.1, he⟩

/-- For unrestricted linear perturbations the physical spectral maximum is exactly sharp. -/
theorem hsGain_eq_spectralGain (h : bezout.History N) (I : SpectralInterval) :
    hsGain h I false = h.spectralGain I := by
  apply le_antisymm (hsGain_le_spectralGain h I false)
  apply le_csInf (hsBounds_nonempty h I false)
  intro C hb
  obtain ⟨x, hx, y, hy, he⟩ := h.spectralGain_attained I
  rw [← he]
  exact hsBound_kernel_lower h I C hb x y hx hy

/-- A single diagonal mode has exactly its scalar Hilbert--Schmidt norm. -/
theorem hsNorm_diagonal_pair (a : ℝ) :
    hsNorm (Matrix.diagonal ![a, 0]) = |a| := by
  simp [hsNorm, hsSq, Fin.sum_univ_two, Matrix.diagonal, Real.sqrt_sq_eq_abs]

/-- Symmetric scalar perturbations force each diagonal physical corner energy. -/
theorem hsBound_diagonal_energy (h : bezout.History N) (I : SpectralInterval)
    (symmetric : Bool) (C : ℝ) (hb : HsBound h I symmetric C)
    (x : ℝ) (hx : x ∈ Set.Icc I.mu I.L) :
    Lower.physicalKernelSq h x x ≤ C ^ 2 := by
  let a : Fin N → ℝ := fun s => Lower.physicalKernel h s x x
  let D : Fin N → Matrix (Fin 2) (Fin 2) ℝ := fun s => Matrix.diagonal ![a s, 0]
  have had := diagonal_pair_admissible I x x hx hx
  have hu := hb.2 (Fin 2) (Matrix.diagonal ![x, x]) had.1 had.2 D
    (fun _ _ => by simp [D, Matrix.IsHermitian])
  have hout : h.matrixResponse (Matrix.diagonal ![x, x]) D =
      Matrix.diagonal ![∑ s, a s ^ 2, 0] := by
    ext i j
    rw [h.diagonal_matrixResponse_entry]
    fin_cases i <;> fin_cases j <;> simp [D, a, Matrix.diagonal, pow_two]
  have hin : ∑ s, hsNorm (D s) ^ 2 = ∑ s, a s ^ 2 := by
    simp only [D, hsNorm_diagonal_pair, sq_abs]
  rw [hout, hin, hsNorm_diagonal_pair,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hu
  exact energy_le_sq_of_aligned (Finset.sum_nonneg fun _ _ => sq_nonneg _) hb.1 hu

/-- Symmetric off-diagonal perturbations retain the sum of the two opposite
physical kernels, exactly the coupling in the stronger four-corner bound. -/
theorem hsBound_symmetric_cross_energy (h : bezout.History N) (I : SpectralInterval)
    (symmetric : Bool) (C : ℝ) (hb : HsBound h I symmetric C) (x y : ℝ)
    (hx : x ∈ Set.Icc I.mu I.L) (hy : y ∈ Set.Icc I.mu I.L) :
    (∑ s, ((Lower.physicalKernel h s x y + Lower.physicalKernel h s y x) / 2) ^ 2) ≤ C ^ 2 := by
  let a : Fin N → ℝ := fun s =>
    (Lower.physicalKernel h s x y + Lower.physicalKernel h s y x) / 2
  let e : ℝ := ∑ s, a s ^ 2
  let D : Fin N → Matrix (Fin 2) (Fin 2) ℝ := fun s =>
    !![0, a s / Real.sqrt 2; a s / Real.sqrt 2, 0]
  let A : ℝ := ∑ s, Lower.physicalKernel h s x y * (a s / Real.sqrt 2)
  let B : ℝ := ∑ s, Lower.physicalKernel h s y x * (a s / Real.sqrt 2)
  have ht : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have he : 0 ≤ e := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have had := diagonal_pair_admissible I x y hx hy
  have hu := hb.2 (Fin 2) (Matrix.diagonal ![x, y]) had.1 had.2 D
    (fun _ _ => by ext i j; fin_cases i <;> fin_cases j <;> simp [D])
  have hD (s : Fin N) : hsNorm (D s) ^ 2 = a s ^ 2 := by
    simp [hsNorm_sq, hsSq, Fin.sum_univ_two, D, div_pow, ht]
  have hout : h.matrixResponse (Matrix.diagonal ![x, y]) D = !![0, A; B, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bezout.History.diagonal_matrixResponse_entry, D, A, B]
  have hAB : A + B = Real.sqrt 2 * e := by
    unfold A B e
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    change _ = Real.sqrt 2 *
      ((Lower.physicalKernel h s x y + Lower.physicalKernel h s y x) / 2) ^ 2
    dsimp only [a]
    field_simp
    nlinarith [sq_nonneg (Lower.physicalKernel h s x y + Lower.physicalKernel h s y x)]
  have hnorm : hsNorm (h.matrixResponse (Matrix.diagonal ![x, y]) D) ^ 2 = A ^ 2 + B ^ 2 := by
    rw [hout, hsNorm_sq]
    simp [hsSq, Fin.sum_univ_two]
  have hproj : e ≤ hsNorm (h.matrixResponse (Matrix.diagonal ![x, y]) D) := by
    have hsq : (A + B) ^ 2 = 2 * e ^ 2 := by rw [hAB, mul_pow, ht]
    nlinarith [hsNorm_nonneg (h.matrixResponse (Matrix.diagonal ![x, y]) D), sq_nonneg (A - B)]
  simp_rw [hD] at hu
  exact energy_le_sq_of_aligned he hb.1 (hproj.trans hu)

/-- The symmetric Hilbert--Schmidt class has the same sharp parity-corrected
lower coefficient, including odd horizons and histories with arbitrary signs. -/
theorem linearGain_le_hsBound (h : bezout.History N) (I : SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 2 ≤ N) (symmetric : Bool) (C : ℝ)
    (hb : HsBound h I symmetric C) : Lower.linearGain I N ≤ C := by
  have hμ := hsBound_diagonal_energy h I symmetric C hb I.mu ⟨le_rfl, I.mu_lt_L.le⟩
  have hL := hsBound_diagonal_energy h I symmetric C hb I.L ⟨I.mu_lt_L.le, le_rfl⟩
  have hs : Lower.linearGain I N ^ 2 ≤ C ^ 2 := by
    by_cases hodd : Odd N
    · have hcross := hsBound_symmetric_cross_energy h I symmetric C hb I.mu I.L
        ⟨le_rfl, I.mu_lt_L.le⟩ ⟨I.mu_lt_L.le, le_rfl⟩
      have hl := Lower.linearGain_sq_le_symmetric_four_corners h I he (by
        have := Nat.odd_iff.mp hodd; omega) hodd
      have heq : Lower.symmetricCornerEnergy
          (fun s => (h.response s).eval I.mu) (fun s => (h.response s).eval I.L)
          (fun s => (h.query s).eval I.mu) (fun s => (h.query s).eval I.L) =
          3 / 8 * (Lower.physicalKernelSq h I.mu I.mu + Lower.physicalKernelSq h I.L I.L) +
            1 / 4 * ∑ s, ((Lower.physicalKernel h s I.mu I.L +
              Lower.physicalKernel h s I.L I.mu) / 2) ^ 2 := by
        unfold Lower.symmetricCornerEnergy Lower.physicalKernelSq Lower.physicalKernel
        simp only [Finset.sum_add_distrib, div_pow, ← Finset.sum_div]
        ring
      rw [heq] at hl
      linarith
    · rw [Lower.linearGain_sq I hN]
      simp only [Lower.linearCorrectionSq, hodd, ite_false, mul_one]
      exact (Lower.scalar_endpoint_lower h I he (by omega)).trans hμ
  exact (sq_le_sq₀ (Lower.linearGain_nonneg I N) hb.1).mp hs

/-- The sharp lower coefficient holds for either Hilbert--Schmidt perturbation class. -/
theorem linearGain_le_hsGain (h : bezout.History N) (I : SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 2 ≤ N) (symmetric : Bool) :
    Lower.linearGain I N ≤ hsGain h I symmetric :=
  le_csInf (hsBounds_nonempty h I symmetric)
    (fun C hb => linearGain_le_hsBound h I he hN symmetric C hb)

end
end bezout.Gains
