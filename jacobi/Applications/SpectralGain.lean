import chebyshev1.Realization.GainBounds

/-!
Article: jacobi, Theorem 5.1.
The closed spectral interval [0,1] includes the zero endpoint. The
first article's first-variation kernels and time norm are reused exactly;
its positive-lower-endpoint interval type is not extended by a false proof.
Use: NesterovGain and UniformBlockGain maximize the same original spectral-pair norm.
-/
namespace jacobi.Applications
noncomputable section
open chebyshev1 Set
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

/-- The genuine spectral-pair gain on the entire unit interval, including its zero endpoint.
Use: the actual Nesterov and terminal-equivalent block gains use the first article's verified first-variation kernel and its original Euclidean time norm.
Article: jacobi, Theorem 5.1.
-/
def unitSpectralGain (R:Realization ι) (k:ℕ) : ℝ :=
  sSup {v:ℝ | ∃ l∈Icc (0:ℝ) 1,∃ u∈Icc (0:ℝ) 1,v=R.kernelNorm k l u}

/-- The actual unit-interval gain values form a compact set.
Use: all full-fibre lower bounds concern a genuine bounded supremum, so no unbounded-set convention enters the optimal block gain.
Article: jacobi, Theorem 5.1.
Proof: the reused original kernel norm is continuous in both spectral variables. Its image of the compact spectral square is exactly the genuine gain-value set. -/
theorem unitSpectralGainValues_compact (R:Realization ι) (k:ℕ) :
    IsCompact {v:ℝ | ∃ l∈Icc (0:ℝ) 1,∃ u∈Icc (0:ℝ) 1,v=R.kernelNorm k l u} := by
  -- Identify the original existential gain set with the continuous image of the closed spectral square.
  have he : {v:ℝ | ∃ l∈Icc (0:ℝ) 1,∃ u∈Icc (0:ℝ) 1,v=R.kernelNorm k l u}=
      (fun p:ℝ × ℝ => R.kernelNorm k p.1 p.2) '' (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
    ext v
    constructor
    · rintro ⟨l,hl,u,hu,rfl⟩
      exact ⟨(l,u),⟨hl,hu⟩,rfl⟩
    · rintro ⟨⟨l,u⟩,⟨hl,hu⟩,rfl⟩
      exact ⟨l,hl,u,hu,rfl⟩
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).image (R.continuous_kernelNorm k)

/-- Every actual spectral-pair norm is bounded above by the genuine unit-interval gain.
Use: transfers arbitrary-fibre endpoint energy lower bounds to the full block-class spectral optimum.
Article: jacobi, Theorem 5.1.
Proof: compactness makes the actual supremum bounded; the chosen physical pair belongs to its original value set. -/
theorem unitSpectralGain_ge (R:Realization ι) (k:ℕ) {l u:ℝ}
    (hl:l∈Icc (0:ℝ) 1) (hu:u∈Icc (0:ℝ) 1) : R.kernelNorm k l u≤unitSpectralGain R k :=
  le_csSup (unitSpectralGainValues_compact R k).bddAbove ⟨l,hl,u,hu,rfl⟩

/-- Simultaneous endpoint domination of the actual insertion kernels gives the exact attained full spectral gain.
Use: turns the proved original Nesterov and U-block kernel inequalities into genuine supremum equalities.
Article: jacobi, Theorem 5.1.
Proof: the nonnegative square-root time norm preserves termwise squared domination. The endpoint pair belongs to the spectral square, making its norm the greatest element of the actual gain-value set. -/
theorem unitSpectralGain_eq_endpoint (R:Realization ι) (k:ℕ)
    (h:∀ s<k,∀ l∈Icc (0:ℝ) 1,∀ v∈Icc (0:ℝ) 1,|R.kernel k s l v|≤|R.kernel k s 0 0|) :
    unitSpectralGain R k=R.kernelNorm k 0 0 := by
  -- Attainment is checked on the full spectral square before replacing its supremum by an endpoint value.
  have hg : IsGreatest {v:ℝ | ∃ l∈Icc (0:ℝ) 1,∃ u∈Icc (0:ℝ) 1,v=R.kernelNorm k l u}
      (R.kernelNorm k 0 0) := by
    refine ⟨⟨0,⟨le_rfl,by norm_num⟩,0,⟨le_rfl,by norm_num⟩,rfl⟩,?_⟩
    rintro v ⟨l,hl,u,hu,rfl⟩
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro s hs
    exact sq_le_sq.mpr (h s (Finset.mem_range.mp hs) l hl u hu)
  exact hg.isLUB.csSup_eq ⟨_,hg.1⟩

end
end jacobi.Applications
