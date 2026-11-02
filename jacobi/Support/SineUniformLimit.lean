import jacobi.Support.SineSupportLimit

/-!
Article: jacobi, Appendix C.3 (sine-product estimates).
The complete original compact-uniform sine-product limit follows from
the proved actual moving-index limit and compactness of the original
mesh ratios. No preselected or assumed asymptotic subsequence is used.
Use: uniform normalization of the genuine top-node polynomial combines three instances of this same source statement with the exact sine-product factorization.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter
open scoped Topology

/-- The original support sine products satisfy the complete printed compact-uniform normalized limit on every closed interior mesh range.
Use: uniform normalization of the genuine top-node polynomial combines three instances of this same source statement with the exact sine-product factorization.
Article: jacobi, Appendix C.3 (sine-product estimates).
Proof: failure of uniformity selects genuine bad mesh indices at cofinally large original degrees. Compactness gives a convergent subsequence of their actual ratios. The proved moving-index sine-product limit and continuity of the printed sine power force its error to zero, contradicting the same positive error bound. -/
theorem support_sineProduct_uniform (a b : ℝ) {s δ B : ℝ} (hs:0<s) (hδ:0<δ) (hB:B<1) :
    ∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀m:ℕ,δ≤(m:ℝ)/(n:ℝ)→(m:ℝ)/(n:ℝ)≤B→
      |(n:ℝ)^(1-s)*sineProduct (step a b n) s m-
        (Gamma s)⁻¹*(sin (π*((m:ℝ)/(n:ℝ)))/π)^(s-1)|<ε := by
  -- Compactness is applied to the actual bad mesh ratios, retaining the original degree and product at every chosen index.
  intro ε hε
  classical
  by_contra h
  push Not at h
  choose ns hns ms hlo hhi hbad using h
  have hnT : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  obtain ⟨t,ht,φ,hφ,hratio⟩ := isCompact_Icc.tendsto_subseq
    (x:=fun k => (ms k:ℝ)/(ns k:ℝ)) (fun k => ⟨hlo k,hhi k⟩)
  have ht0 : t∈Ioo (0:ℝ) 1 := ⟨hδ.trans_le ht.1,ht.2.trans_lt hB⟩
  have hprod := support_sineProduct_limit a b hs ht0 (hnT.comp hφ.tendsto_atTop) hratio
  have hsin : 0<sin (π*t)/π := div_pos
    (sin_pos_of_pos_of_lt_pi (mul_pos pi_pos ht0.1) (by nlinarith [pi_pos,ht0.2])) pi_pos
  have hfun := (((Real.continuous_sin.continuousAt.tendsto.comp (hratio.const_mul π)).div_const π).rpow_const
    (p:=s-1) (Or.inl hsin.ne')).const_mul (Gamma s)⁻¹
  have herror := hprod.sub hfun
  simp only [sub_self] at herror
  obtain ⟨k,hk⟩ := (herror.norm.eventually (Iio_mem_nhds (by simpa only [norm_zero] using hε))).exists
  have hk' : |(ns (φ k):ℝ)^(1-s)*sineProduct (step a b (ns (φ k))) s (ms (φ k))-
      (Gamma s)⁻¹*(sin (π*((ms (φ k):ℝ)/(ns (φ k):ℝ)))/π)^(s-1)|<ε := by
    simpa only [Function.comp_def,Real.norm_eq_abs] using hk
  exact (not_lt_of_ge (hbad (φ k))) hk'

end
end jacobi.Support
