import jacobi.Comparison.WeightNormalization

/-!
Article: jacobi, Theorem 2.1.
The actual normalized target/support probabilities satisfy the full
uniform inverse-square error bound with a single index-independent
error epsilon_N such that N*epsilon_N tends to zero. The fixed-index
identification with rho still requires the separate finite-product
limit; it is not a premise or a conclusion of this module.
Use: the target eigenvector tail bound combines this literal probability comparison with the independently proved support-weight bounds of Appendix C.3.
-/
namespace jacobi.Comparison
noncomputable section
open Real Filter jacobi.Support
open scoped Topology

/-- The original target/support probability ratios are uniformly positive and bounded at every growing spectral index.
Use: the target eigenvector tail bound combines this literal probability comparison with the independently proved support-weight bounds of Appendix C.3.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the exact original ratio is the original positive relative gap product divided by its literal support-weighted normalizer. Both numerator and denominator have independently proved uniform positive lower and upper bounds. -/
theorem comparisonWeight_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀k:Fin (n+1),
      c≤(targetMeasure a b ha hb n).weight k/(supportMeasure a b ha hb n).weight k ∧
      (targetMeasure a b ha hb n).weight k/(supportMeasure a b ha hb n).weight k≤C := by
  -- The product and its probability-weighted normalizer have separate proved positive bounds.
  obtain ⟨c₁,C₁,D,hc₁,hC₁,hD,h₁⟩ := relativeGapProduct_bounds ha hb
  obtain ⟨c₂,C₂,hc₂,hC₂,h₂⟩ := comparisonNormalizer_bounds ha hb
  refine ⟨c₁/C₂,C₁/c₂,by positivity,by positivity,?_⟩
  filter_upwards [h₁,h₂] with n hn₁ hn₂
  intro k
  rw [comparisonWeight_ratio]
  change c₁/C₂≤relativeGapProduct a b ha hb n k/comparisonNormalizer a b ha hb n ∧
    relativeGapProduct a b ha hb n k/comparisonNormalizer a b ha hb n≤C₁/c₂
  exact ⟨div_le_div₀ (relativeGapProduct_pos a b ha hb n k).le (hn₁ k).1 (comparisonNormalizer_pos a b ha hb n) hn₂.2,
    div_le_div₀ hC₁.le (hn₁ k).2.1 hc₂ hn₂.1⟩

/-- The actual target/support weight ratios have the complete printed uniform error estimate with a genuine index-independent little-o remainder.
Use: the two-edge Gram spectral tail sums these actual errors, and the bound N*epsilon_N->0 makes the common bulk remainder vanish after summing all original nodes.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: write the exact normalized ratio as R/S. The triangle inequality bounds |R-S| by |R-1|+|S-1|. Divide by the proved positive lower bound for the actual normalizer. The inverse-square product error gives the fixed coefficient; the original bulk term and actual normalizer error give one common epsilon_N. Their matrix-size-scaled limits have both been proved independently. -/
theorem comparisonWeight_error {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∃ε:ℕ→ℝ,(∀n,0≤ε n) ∧
      Tendsto (fun n:ℕ => ((n:ℝ)+1)*ε n) atTop (𝓝 0) ∧
      ∀ᶠn:ℕ in atTop,∀k:Fin (n+1),
        |(targetMeasure a b ha hb n).weight k/(supportMeasure a b ha hb n).weight k-1|≤
          C/(jacobi.Jacobi.edgeIndex (n+1) k.val:ℝ)^2+ε n := by
  -- The same original finite normalizer controls every spectral index simultaneously.
  obtain ⟨c₁,C₁,D,hc₁,hC₁,hD,h₁⟩ := relativeGapProduct_bounds ha hb
  obtain ⟨c,C,hc,hC,h₂⟩ := comparisonNormalizer_bounds ha hb
  let ε (n:ℕ) : ℝ := (D*(log ((n:ℝ)+1)/((n:ℝ)+1)^2)+|comparisonNormalizer a b ha hb n-1|)/c
  refine ⟨D/c,by positivity,ε,?_,?_,?_⟩
  · intro n
    have hlog : 0≤log ((n:ℝ)+1) := log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])
    dsimp [ε]
    positivity
  · have hN : Tendsto (fun n:ℕ => (n:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hlog : Tendsto (fun n:ℕ => log ((n:ℝ)+1)/((n:ℝ)+1)) atTop (𝓝 0) := by
      simpa only [pow_one,one_mul,add_zero,Function.comp_def] using (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hN
    have ht := ((hlog.const_mul D).add (comparisonNormalizer_error ha hb)).div_const c
    simp only [mul_zero,add_zero,zero_div] at ht
    exact ht.congr' (Eventually.of_forall (fun n => by
      dsimp [ε]
      have hN0 : (n:ℝ)+1≠0 := by positivity
      field_simp))
  · filter_upwards [h₁,h₂] with n hn₁ hn₂
    intro k
    let R := relativeGapProduct a b ha hb n k
    let S := comparisonNormalizer a b ha hb n
    have hS : 0<S := comparisonNormalizer_pos a b ha hb n
    have hlog : 0≤log ((n:ℝ)+1) := log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])
    have hsum : |R-S|≤|R-1|+|S-1| := by
      have h := abs_sub_le R 1 S
      simpa only [abs_sub_comm 1 S] using h
    have hnum : |R-S|≤D*(1/(jacobi.Jacobi.edgeIndex (n+1) k.val:ℝ)^2+log ((n:ℝ)+1)/((n:ℝ)+1)^2)+|S-1| :=
      hsum.trans (add_le_add (hn₁ k).2.2 le_rfl)
    rw [comparisonWeight_ratio]
    change |R/S-1|≤_
    calc
      _ = |R-S|/S := by rw [div_sub_one hS.ne',abs_div,abs_of_pos hS]
      _ ≤ (D*(1/(jacobi.Jacobi.edgeIndex (n+1) k.val:ℝ)^2+log ((n:ℝ)+1)/((n:ℝ)+1)^2)+|S-1|)/c :=
        div_le_div₀ (by positivity) hnum hc hn₂.1
      _ = _ := by dsimp [ε,S]; ring

end
end jacobi.Comparison
