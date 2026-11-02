import jacobi.Support.SineGamma
import jacobi.Bessel.ZeroGeometry

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The exact positive rising-factor quotient satisfies uniform two-sided
power bounds at every index, including the entire small-index prefix.
The Gamma normalization is the genuine proved Euler limit.
Use: risingRatio_bounds combines the genuine tail limit with positivity at every actual small index.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The original rising-factor quotient has its exact positive normalized limit with a shifted degree, including a normalization well-defined at zero.
Use: risingRatio_bounds combines the genuine tail limit with positivity at every actual small index.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: multiply the previously proved actual Gamma quotient limit by ((m+1)/m)^(1-s), whose limit is one. For positive degree the real-power division identity cancels the true degree normalization. -/
theorem risingRatio_shifted_limit {s : ℝ} (hs:0<s) :
    Tendsto (fun m : ℕ => ((m:ℝ)+1)^(1-s)*
      (∏j∈Finset.range m,((j:ℝ)+s)/((j:ℝ)+1))) atTop (𝓝 ((Gamma s)⁻¹)) := by
  -- The shifted normalization retains every actual zero-degree value while its limit uses only positive degrees.
  have hP := (shifted_nat_ratio 1 0).rpow_const (p:=1-s) (Or.inl one_ne_zero)
  simp only [add_zero,one_rpow] at hP
  have h := (risingRatio_limit hs).mul hP
  simp only [mul_one] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hm0 : (0:ℝ)<m := by exact_mod_cast hm
  rw [Real.div_rpow (by positivity : (0:ℝ)≤(m:ℝ)+1) hm0.le]
  field_simp [(Real.rpow_pos_of_pos hm0 (1-s)).ne']

/-- Every actual positive rising-factor quotient satisfies the original two-sided power bound with constants valid at all genuine indices.
Use: sineProduct_power_bounds combines these bounds with the quantitatively controlled smooth correction to prove the source sine-product bounds without numerical prefix checks.
Article: jacobi, Appendix C.3 (sine-product estimates).
Proof: the actual normalized quotient has a positive genuine limit and is positive at every original small index. The existing finite-prefix absorption lemma supplies a positive lower bound; convergence supplies a global upper bound. Divide by the same positive normalization power. -/
theorem risingRatio_bounds {s : ℝ} (hs:0<s) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀m:ℕ,
      c*((m:ℝ)+1)^(s-1)≤(∏j∈Finset.range m,((j:ℝ)+s)/((j:ℝ)+1)) ∧
      (∏j∈Finset.range m,((j:ℝ)+s)/((j:ℝ)+1))≤C*((m:ℝ)+1)^(s-1) := by
  -- Positivity controls the complete original finite prefix, rather than treating it as an external certificate.
  let f : ℕ→ℝ := fun m => ((m:ℝ)+1)^(1-s)*∏j∈Finset.range m,((j:ℝ)+s)/((j:ℝ)+1)
  have hf : ∀m,0<f m := by
    intro m
    apply mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    apply Finset.prod_pos
    intro j hj
    exact div_pos (by linarith [Nat.cast_nonneg j (α:=ℝ)]) (by positivity)
  have hl := risingRatio_shifted_limit hs
  have hG : 0<(Gamma s)⁻¹ := inv_pos.mpr (Gamma_pos_of_pos hs)
  have he : ∀ᶠm:ℕ in atTop,(Gamma s)⁻¹/2≤f m :=
    (hl.eventually (Ioi_mem_nhds (show (Gamma s)⁻¹/2<(Gamma s)⁻¹ by linarith))).mono (fun _ h => h.le)
  obtain ⟨c,hc,hlo⟩ := jacobi.Bessel.positive_lower_all hf (by positivity : 0<(Gamma s)⁻¹/2) he
  obtain ⟨C,hhi⟩ := hl.bddAbove_range
  have hC : 0<C := lt_of_lt_of_le (hf 0) (hhi (Set.mem_range_self 0))
  refine ⟨c,C,hc,hC,?_⟩
  intro m
  have hp : 0<((m:ℝ)+1)^(s-1) := Real.rpow_pos_of_pos (by positivity) _
  have heq : f m=(∏j∈Finset.range m,((j:ℝ)+s)/((j:ℝ)+1))/((m:ℝ)+1)^(s-1) := by
    dsimp [f]
    rw [show (1-s:ℝ)= -(s-1) by ring,Real.rpow_neg (by positivity)]
    ring
  refine ⟨(le_div_iff₀ hp).mp ?_,(div_le_iff₀ hp).mp ?_⟩
  · rw [← heq]; exact hlo m
  · rw [← heq]; exact hhi (Set.mem_range_self m)

end
end jacobi.Support
