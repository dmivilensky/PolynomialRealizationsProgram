import jacobi.Support.TopUniformLimit
import jacobi.Support.PolynomialNodeParity

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Exact physical parity extends the proved top-node limit to the full
original chain, including both endpoints. No new limiting profile
or reflected-polynomial assumption is introduced.
Use: topValue_full_uniform matches the exact reversed original mesh to the same original Gamma-normalized profile.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The original exact top-node continuum profile is symmetric about the physical midpoint.
Use: topValue_full_uniform matches the exact reversed original mesh to the same original Gamma-normalized profile.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: sin(pi*(1-t))=sin(pi*t), so the original power and Gamma constant agree exactly. -/
theorem topProfile_reflection (a b t:ℝ) : topProfile a b (1-t)=topProfile a b t := by
  simp [topProfile,mul_sub]

/-- The original top-node polynomial converges uniformly to its actual Gamma-normalized sine profile on the full original physical chain.
Use: topValue_square_norm_limit computes the genuine full top-node spectral normalization from the actual polynomial values at both edges.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: use the proved half-chain uniform limit directly on the first half. On the second half, exact original eigenvector parity replaces m by n-m; the original profile has precisely the matching physical reflection symmetry. -/
theorem topValue_full_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀m:ℕ,m≤n→
      |(n:ℝ)^(-gamma a)*topValue a b ha hb n m-topProfile a b ((m:ℝ)/(n:ℝ))|<ε := by
  -- The exact original finite reversal matches the same n-m mesh, so neither the normalization nor the endpoint profile changes.
  intro ε hε
  obtain ⟨N,hN⟩ := topValue_uniform ha hb ε hε
  refine ⟨max N 1,?_⟩
  intro n hn m hm
  have hnN : N≤n := (le_max_left _ _).trans hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  by_cases hhalf:2*m≤n
  · exact hN n hnN m hhalf
  · have h := hN n hnN (n-m) (by omega)
    have hr := topValue_rev a b ha hb n (⟨m,by omega⟩:Fin (n+1))
    simp only [Fin.val_rev,Nat.add_sub_add_right] at hr
    have hmesh : ((n-m:ℕ):ℝ)/(n:ℝ)=1-(m:ℝ)/(n:ℝ) := by
      rw [Nat.cast_sub hm]
      field_simp
    simpa only [hr,hmesh,topProfile_reflection] using h

end
end jacobi.Support
