import «2606.16671v2».SineJacobi.ProfileEnergy

/-!
Article: 2606.16671v2, Theorem E.3.
E.4's second discrete sum, expressed in the original endpoint values.
Result: `«2606.16671v2».SineJacobi.endpoint_product_square_sum_limit` supplies the stated article
conclusion.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Filter Topology MeasureTheory Set
open scoped BigOperators ENNReal

/--
The explicit normalization C_N=√π in Lemma E.4.

Exact identity `endpointProfile N t = endpoint N (Nat.floor ((N:ℝ)*t))/(sqrt Real.pi*sqrt
(N:ℝ))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem E.3.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem endpointProfile_sqrt_pi (N : ℕ) (t : ℝ) :
    endpointProfile N t = endpoint N (Nat.floor ((N:ℝ)*t))/(sqrt Real.pi*sqrt (N:ℝ)) := by rw [endpointProfile, sqrt_mul pi_pos.le]

/--
E.4's first discrete sum; the finite value is already exactly I_sin.

Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ => (∑
s ∈ Finset.range N, endpoint N s*endpoint N (N-s-1))/(Real.pi*(N:ℝ)^2)) atTop (𝓝
sineIntegral)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Theorem E.3.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem endpoint_product_sum_limit :
    Tendsto (fun N : ℕ => (∑ s ∈ Finset.range N,
      endpoint N s*endpoint N (N-s-1))/(Real.pi*(N:ℝ)^2))
      atTop (𝓝 sineIntegral) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [sineIntegral_eq]
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  change 1/Real.pi = (∑ s ∈ Finset.range N, greenWeight N s)/(Real.pi*(N:ℝ)^2)
  rw [greenWeight_sum ⟨1,2,by norm_num,by norm_num⟩ N hN]
  field_simp [hn]

/--
E.4's second discrete sum, expressed in the original endpoint values.

Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ => (∑
s ∈ Finset.range N, (endpoint N s*endpoint N (N-s-1))^2)/(Real.pi^2*(N:ℝ)^3)) atTop (𝓝 (∫ t in
(0:ℝ)..1, (sineProfile t*sineProfile (1-t))^2))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Theorem E.3.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem endpoint_product_square_sum_limit :
    Tendsto (fun N : ℕ => (∑ s ∈ Finset.range N,
      (endpoint N s*endpoint N (N-s-1))^2)/(Real.pi^2*(N:ℝ)^3))
      atTop (𝓝 (∫ t in (0:ℝ)..1, (sineProfile t*sineProfile (1-t))^2)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hh := greenWeight_energy_limit.div_const (Real.pi^2)
  have he : sineEnergy/Real.pi^2 =
      ∫ t in (0:ℝ)..1, (sineProfile t*sineProfile (1-t))^2 := by
    unfold sineEnergy sineDensity profileProduct
    simp only [mul_pow]
    rw [intervalIntegral.integral_const_mul]
    field_simp
  rw [he] at hh
  convert hh using 1
  funext N
  simp only [greenWeight]
  ring

end
end «2606.16671v2».SineJacobi
