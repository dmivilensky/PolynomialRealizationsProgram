import polyak.FiniteHorizon.SourcePrefactor
import polyak.Regularity.MemoryRight

/-!
Article: Appendix C, actual physical factors also preserve the finite-memory rate.
Use: the exact finite Gram factors give the strict inequality for the original
normalized dual weights, retaining lag support at most five. No independent
choice of a boundary dual or certificate is assumed.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Boundary Regularity Set Filter
open scoped Topology

theorem GramFactors.nonneg {D : ℕ} {F : FrequencyCircle → ℝ}
    (cert : GramFactors D F) (θ : FrequencyCircle) : 0≤F θ := by
  rw [cert.exact]
  exact Finset.sum_nonneg fun _ _ => fourierGram_nonneg _ _ _

theorem HasPhysicalFactors7.exists_strictCertificate {q t γ ε : ℝ} (hq : 0<q)
    (hf : HasPhysicalFactors7 q t) (hγ : 0≤γ) (hε : 0<ε)
    (huv : Real.sinh (V t)≤Real.sinh (t-Real.log q))
    (hsmall : 4*γ≤Real.sinh (t-Real.log q)^2-Real.sinh (V t)^2)
    (hgap : ε≤(Real.cosh t-1)*(Real.sinh (t-Real.log q)^2-Real.sinh (V t)^2)+
      2*γ*Real.sinh (t-Real.log q)^2) :
    ∃ cert : Duality.StrictCertificate (Waves.multiplierMap 0 (2*q) (q^2) t) t,
      ∀ n∈cert.lags,n≤5 := by
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
  refine ⟨strictCertificateOfWeights W (t-Real.log q) t γ ε hγ hε hs,?_⟩
  intro n hn
  change n∈insert 1 W.lags at hn
  rcases Finset.mem_insert.mp hn with rfl|hn
  · omega
  · exact hW n hn

theorem memory_rate_eq_of_right_physical_source {q v' : ℝ} (hq : 0<q) (hq1 : q<1)
    (hd : HasDerivWithinAt V v' (Ici (T q)) (T q)) (hv' : v'<1)
    (hfactory : ∀ᶠ t in 𝓝[≥] (T q),HasPhysicalFactors7 q t) :
    ∀ᶠ H : ℕ in atTop,growthRate 0 (2*q) (q^2) H=Real.exp (T q) := by
  let g:=rightExtension V v' (T q)
  have hg : HasDerivAt g v' (T q):=rightExtension_hasDerivAt hd
  have hg0 : g (T q)=V (T q):=rightExtension_eq le_rfl
  have heq : T q-Real.log q=g (T q):=by rw [hg0]; exact T_sub_log_eq_V hq hq1
  have hgpos : 0<g (T q):=by rw [←heq]; exact actual_twist_pos hq hq1
  obtain ⟨a,b,η,ha,_,hη,_,hmargins⟩:=exists_polyak_linear_margins hg hv' hgpos heq
  apply memory_rate_eq_of_eventual_right_certificates hq
  have hfactory' : ∀ᶠ t in 𝓝[>] (T q),HasPhysicalFactors7 q t:=
    hfactory.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hnear : ∀ᶠ t in 𝓝 (T q),t<T q+η:=eventually_lt_nhds (by linarith : T q<T q+η)
  filter_upwards [hfactory',hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
    with t hf ht hgt
  have hδ : 0<t-T q:=sub_pos.mpr hgt
  have hδη : t-T q≤η:=by linarith
  have hm:=hmargins (t-T q) hδ hδη
  have het : T q+(t-T q)=t:=by ring
  rw [het] at hm
  have hge : g t=V t:=rightExtension_eq hgt.le
  rw [hge] at hm
  obtain ⟨_,huv,hγ,_,hsmall,hgap⟩:=hm
  exact hf.exists_strictCertificate hq hγ (mul_pos ha hδ) huv hsmall hgap

end polyak.FiniteHorizon
