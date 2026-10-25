import polyak.FiniteHorizon.Noncentral

/-!
Article: Appendix C, the closed P₂ endpoint at the positive exponent.
Use: increasing cosh puts the right exponent germ inside the proved P₂ arc.
The negative exponent at this endpoint belongs to the neighboring P₅ germ.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Spectral Boundary Regularity Set Filter
open scoped Topology

theorem eventually_cosh_ge_of_nonneg {t G : ℝ} (ht : 0≤t) (hG : G≤Real.cosh t) :
    ∀ᶠ s in 𝓝[≥] t,G≤Real.cosh s := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  apply hG.trans
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg ht,abs_of_nonneg (ht.trans hs)]
  exact hs

theorem positive_Ga_right_derivative {t : ℝ} (ht : 0≤t) (ha : Real.cosh t=P2.Ga) :
    HasDerivWithinAt V (P2.boundaryDerivative P2.zetaA t) (Ici t) t ∧
      |P2.boundaryDerivative P2.zetaA t|<1 := by
  have hz : P2.zetaA∈Icc P2.zeta1 P2.zetaA:=⟨P2.zeta1_lt_zetaA.le,le_rfl⟩
  have he : Real.cosh t=P2.G P2.zetaA:=ha
  refine ⟨?_,P2.abs_boundaryDerivative_lt_one P2.zetaA_mem he⟩
  apply (P2.hasDerivWithinAt_V hz he).mono_of_mem_nhdsWithin
  have hu : ∀ᶠ s in 𝓝 t,Real.cosh s<G1:=
    Real.continuous_cosh.continuousAt.eventually (gt_mem_nhds (by rw [ha]; exact P2.Ga_lt_G1))
  filter_upwards [hu.filter_mono nhdsWithin_le_nhds,eventually_cosh_ge_of_nonneg ht ha.ge]
    with s hs hsa
  exact ⟨hsa,hs.le⟩

theorem memory_rate_eq_positive_Ga {q : ℝ} (hq : 0<q) (hq1 : q<1)
    (ht : 0≤T q) (ha : Real.cosh (T q)=P2.Ga) :
    ∀ᶠ H : ℕ in atTop,growthRate 0 (2*q) (q^2) H=Real.exp (T q) := by
  have hd:=positive_Ga_right_derivative ht ha
  apply memory_rate_eq_of_right_boundary (M:=3) hq hq1 (by omega) hd.1 (abs_lt.mp hd.2).2
  have hn:=eventually_cosh_ge_of_nonneg ht ha.ge
  filter_upwards [hn.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)] with t ht
  exact exists_noncentral_dual ht

theorem exists_uniform_prefactor_positive_Ga {q : ℝ} (hq : 0<q) (hq1 : q<1)
    (ht : 0≤T q) (ha : Real.cosh (T q)=P2.Ga) :
    ∃ H : ℕ,7≤H ∧ ∃ C : ℝ,0<C ∧ ∀ n : ℕ,
      envelope 0 (2*q) (q^2) H n≤C*Real.exp ((n : ℝ)*T q) := by
  obtain ⟨H,hRate,hH⟩:=((memory_rate_eq_positive_Ga hq hq1 ht ha).and (eventually_ge_atTop 7)).exists
  have hd:=positive_Ga_right_derivative ht ha
  have heq:=T_sub_log_eq_V hq hq1
  have hVT : 0<V (T q):=by rw [←heq]; exact actual_twist_pos hq hq1
  refine ⟨H,hH,?_⟩
  apply exists_prefactor_of_right_source_germ hq hd.1 (abs_lt.mp hd.2).2 hVT heq hH hRate.le
  filter_upwards [eventually_cosh_ge_of_nonneg ht ha.ge] with t ht
  exact hasPhysicalFactors7_of_cosh_ge_Ga hq ht

end polyak.FiniteHorizon
