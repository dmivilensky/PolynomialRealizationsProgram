import jacobi.Support.TopValueLimit
import jacobi.Support.TopZeroLimit
import jacobi.Support.TopDifference

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The actual degree half-prefix has its uniform top-node continuum
limit down to zero. TopHalfUniform proves the stronger full matrix
half-prefix 2*m<=n+1, including the possible extra middle coordinate.
Use: TopFullUniform applies this degree-prefix form to the original symmetric ground profile. TopHalfUniform supplies the stronger full matrix half-prefix used by the complex edge and Gram limits.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The actual support top-node polynomial converges uniformly on its degree half-prefix to the printed Gamma-normalized profile, including zero.
Use: TopFullUniform applies this degree-prefix form to the original symmetric ground profile. TopHalfUniform supplies the stronger full matrix half-prefix used by the complex edge and Gram limits.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: a failure of uniformity selects actual bad mesh points at cofinally large original degrees. Their ratios have a convergent subsequence in the closed source half interval. The proved actual moving-index limit handles every positive limiting ratio, and the genuine small-index power bound handles zero. Continuity of the same exact U profile gives a contradiction. -/
theorem topValue_uniform {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀m:ℕ,2*m≤n→
      |(n:ℝ)^(-gamma a)*topValue a b ha hb n m-topProfile a b ((m:ℝ)/(n:ℝ))|<ε := by
  -- The compactness argument retains each actual original polynomial and mesh point; no auxiliary asymptotic profile is assumed.
  intro ε hε
  classical
  by_contra h
  push Not at h
  choose ns hns ms hmesh hbad using h
  have hnT : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  have hratios (k : ℕ) : (ms k:ℝ)/(ns k:ℝ)∈Icc (0:ℝ) (1/2) := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),?_⟩
    by_cases hzero:ns k=0
    · simp [hzero]
    · have hn0 : (0:ℝ)<ns k := by exact_mod_cast (Nat.pos_of_ne_zero hzero)
      apply (div_le_iff₀ hn0).mpr
      have hmr : 2*(ms k:ℝ)≤ns k := by exact_mod_cast hmesh k
      linarith
  obtain ⟨t,ht,φ,hφ,hratio⟩ := isCompact_Icc.tendsto_subseq (x:=fun k => (ms k:ℝ)/(ns k:ℝ)) hratios
  have htop : Tendsto (fun k => (ns (φ k):ℝ)^(-gamma a)*topValue a b ha hb (ns (φ k)) (ms (φ k))) atTop
      (𝓝 (topProfile a b t)) := by
    by_cases ht0:t=0
    · subst t
      simpa only [topProfile_zero ha,Function.comp_def] using topValue_zero_limit ha hb (hnT.comp hφ.tendsto_atTop) hratio
    · exact topValue_limit ha hb ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),by linarith [ht.2]⟩
        (hnT.comp hφ.tendsto_atTop) hratio
  have hfun := (topProfile_continuous (b:=b) ha).continuousAt.tendsto.comp hratio
  have herror := htop.sub hfun
  simp only [sub_self] at herror
  obtain ⟨k,hk⟩ := (herror.norm.eventually (Iio_mem_nhds (by simpa only [norm_zero] using hε))).exists
  have hk' : |(ns (φ k):ℝ)^(-gamma a)*topValue a b ha hb (ns (φ k)) (ms (φ k))-
      topProfile a b ((ms (φ k):ℝ)/(ns (φ k):ℝ))|<ε := by
    simpa only [Function.comp_def,Real.norm_eq_abs] using hk
  exact (not_lt_of_ge (hbad (φ k))) hk'

end
end jacobi.Support
