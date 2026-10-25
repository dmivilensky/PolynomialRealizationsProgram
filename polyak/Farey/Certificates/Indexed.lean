import polyak.Levels.Realization.ExactThreshold

/-! A finite indexed family of signed lag weights gives a literal
certificate; repeated lag indices are combined, with no loss of mass. -/
noncomputable section
namespace polyak.Farey.Certificates
open Levels Set
open scoped BigOperators

variable {I:Type*} [Fintype I]

def indexedSymbol (Θ:Curve) (n:I→ℤ) (a:I→ℝ) (γ:ℝ)
    (hn:∀i,n i≠0) (ha:∀i,0≤a i) (hγ:0≤γ) : CertificateSymbol Θ nonzeroLags := by
  classical
  exact {
    lags:=Finset.univ.image n
    lags_subset:=by intro k hk; obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hk; exact hn i
    weight:=fun k=>∑i,if n i=k then a i else 0
    weight_nonneg:=by intro k _; apply Finset.sum_nonneg; intro i _; split_ifs; exact ha i; exact le_rfl
    gamma:=γ
    gamma_nonneg:=hγ }

theorem indexedSymbol_eval (Θ:Curve) (n:I→ℤ) (a:I→ℝ) (γ:ℝ)
    (hn:∀i,n i≠0) (ha:∀i,0≤a i) (hγ:0≤γ) (ω:Frequency) :
    (indexedSymbol Θ n a γ hn ha hγ).eval ω=
      (∑i,a i*Θ.lag (n i) ω)+γ*Θ.minimizer ω := by
  classical
  dsimp [indexedSymbol,CertificateSymbol.eval]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul,zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_image,Finset.mem_univ,true_and,exists_apply_eq_apply,ite_true]

theorem strictSymbol_of_pointwise_negative {Θ:Curve} {𝒩:Set ℤ}
    (S:CertificateSymbol Θ 𝒩) (hS:∀ω,S.eval ω<0) : Nonempty (StrictSymbol Θ 𝒩) := by
  obtain ⟨ω,_hω,hmax⟩:=isCompact_univ.exists_isMaxOn (Set.univ_nonempty)
    S.continuous_eval.continuousOn
  refine ⟨S,-S.eval ω,neg_pos.mpr (hS ω),?_⟩
  intro x
  simpa only [neg_neg] using (show S.eval x≤S.eval ω from hmax (Set.mem_univ x))

theorem indexed_negative_rate_lt_one (q:General.Tuning) (n:I→ℤ) (a:I→ℝ) (γ:ℝ)
    (hn:∀i,n i≠0) (ha:∀i,0≤a i) (hγ:0≤γ)
    (hneg:∀ω:Frequency,(∑i,a i*(tuningCurve q).lag (n i) ω)+
      γ*(tuningCurve q).minimizer ω<0) : q.rate<1 := by
  apply (rate_lt_one_iff_strictSymbol q).mpr
  apply strictSymbol_of_pointwise_negative (indexedSymbol (tuningCurve q) n a γ hn ha hγ)
  intro ω
  rw [indexedSymbol_eval]
  exact hneg ω

end polyak.Farey.Certificates
