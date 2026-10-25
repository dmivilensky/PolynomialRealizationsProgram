import polyak.FiniteHorizon.GlobalPrefactor

/-!
Article: Appendix C, Lemma lineargap with every source obligation discharged.
Use: every q∈(0,1) has actual finite interpolation certificates with a gap
exactly aδ, lags at most five, and every multiplier bounded in absolute value
by one, uniformly as δ decreases to zero.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Boundary Regularity Set Filter
open scoped Topology

theorem HasPhysicalFactors7.exists_bounded_strictCertificate {q t γ ε : ℝ} (hq : 0<q)
    (hf : HasPhysicalFactors7 q t) (hγ : 0≤γ) (hγ1 : γ≤1) (hε : 0<ε)
    (huv : Real.sinh (V t)≤Real.sinh (t-Real.log q))
    (hsmall : 4*γ≤Real.sinh (t-Real.log q)^2-Real.sinh (V t)^2)
    (hgap : ε≤(Real.cosh t-1)*(Real.sinh (t-Real.log q)^2-Real.sinh (V t)^2)+
      2*γ*Real.sinh (t-Real.log q)^2) :
    ∃ cert : Duality.StrictCertificate (Waves.multiplierMap 0 (2*q) (q^2) t) t,
      (∀ n∈cert.lags,n≤5) ∧ cert.ε=ε ∧
      (∀ n∈cert.lags,|cert.α n|≤1 ∧ |cert.β n|≤1) ∧
        |cert.γplus|≤1 ∧ |cert.γminus|≤1 := by
  obtain ⟨W,hW,hfactors⟩:=hf
  obtain ⟨data⟩:=hfactors γ ε hγ huv hsmall hgap
  have hs : ∀ c : Frequency,dualSymbol W (Real.sinh (t-Real.log q)) (Real.cosh t) c+
      2*γ*Spectral.g (Real.sinh (t-Real.log q)) c≤ -ε:=by
    intro c
    have hh:=data.factors.nonneg (Real.arccos c : FrequencyCircle)
    rw [normalizedMatrix7_symbol W hq t γ hγ hW,frequencyCosine_coe,
      Real.cos_arccos c.property.1 c.property.2] at hh
    linarith
  rw [Waves.multiplierMap_polyak q t hq]
  let cert:=strictCertificateOfWeights W (t-Real.log q) t γ ε hγ hε hs
  refine ⟨cert,?_,rfl,?_,?_,?_⟩
  · intro n hn
    change n∈insert 1 W.lags at hn
    rcases Finset.mem_insert.mp hn with rfl|hn
    · omega
    · exact hW n hn
  · intro n hn
    rw [abs_of_nonneg (cert.α_nonneg n hn),abs_of_nonneg (cert.β_nonneg n hn)]
    exact ⟨lowerWeight_le_one n,upperWeight_le_one W (Real.one_le_cosh t) n⟩
  · change |γ|≤1
    rwa [abs_of_nonneg hγ]
  · change |γ|≤1
    rwa [abs_of_nonneg hγ]

/-- Lemma lineargap on the complete actual parameter domain, including every
switch and the critical exponent. The original strict symbol is part of cert. -/
theorem actual_lineargap {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    ∃ a δ₀ : ℝ,0<a ∧ 0<δ₀ ∧ ∀ δ : ℝ,0<δ → δ≤δ₀ →
      ∃ cert : Duality.StrictCertificate (Waves.multiplierMap 0 (2*q) (q^2) (T q+δ)) (T q+δ),
        (∀ n∈cert.lags,n≤5) ∧ cert.ε=a*δ ∧
        (∀ n∈cert.lags,|cert.α n|≤1 ∧ |cert.β n|≤1) ∧
          |cert.γplus|≤1 ∧ |cert.γminus|≤1 := by
  obtain ⟨v',hd,hv'⟩:=exists_global_right_derivative (T q)
  let g:=rightExtension V v' (T q)
  have hg : HasDerivAt g v' (T q):=rightExtension_hasDerivAt hd
  have hg0 : g (T q)=V (T q):=rightExtension_eq le_rfl
  have heq : T q-Real.log q=g (T q):=by rw [hg0]; exact T_sub_log_eq_V hq hq1
  have hgpos : 0<g (T q):=by rw [←heq]; exact actual_twist_pos hq hq1
  obtain ⟨a,b,η,ha,_,hη,_,hmargins⟩:=exists_polyak_linear_margins hg (abs_lt.mp hv').2 hgpos heq
  refine ⟨a,η,ha,hη,fun δ hδ hδη => ?_⟩
  have hm:=hmargins δ hδ hδη
  have hge : g (T q+δ)=V (T q+δ):=rightExtension_eq (by linarith)
  rw [hge] at hm
  obtain ⟨_,huv,hγ,hγ1,hsmall,hgap⟩:=hm
  exact (hasPhysicalFactors7_global hq (T q+δ)).exists_bounded_strictCertificate hq
    hγ hγ1 (mul_pos ha hδ) huv hsmall hgap

end polyak.FiniteHorizon
