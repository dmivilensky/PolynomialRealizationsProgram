import polyak.FiniteHorizon.SourcePrefactor
import polyak.Regularity.MemoryRight
import polyak.Regularity.OuterArcs

/-!
Article: Appendix C, exact prefactors on every noncentral source arc.
Use: source derivatives at the two switches are taken from the right exponent
germ. Concrete bounded-lag duals and physical factors discharge the memory and
price construction hypotheses, including both signs of the exponent.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Spectral Boundary Regularity Set Filter
open scoped Topology

/-- The actual closed source arcs provide a dual with support at most three. -/
theorem exists_noncentral_dual {t : ℝ} (ha : P2.Ga≤Real.cosh t) :
    ∃ W : DualWeights,(∀ n∈W.lags,n≤3) ∧ 0≤Real.sinh (V t) ∧
      ∀ c : Frequency,0≤(dualPolynomial W (Real.sinh (V t)) (Real.cosh t)).eval (c : ℝ) := by
  by_cases hG : Real.cosh t≤G1
  · obtain ⟨z,hz,_⟩:=P2.p2_arc ⟨ha,hG⟩
    have hm:=P2.arc_mem_interval hz.1
    refine ⟨P2.dualWeights z hm,?_,?_,?_⟩
    · intro n hn
      change n∈({2,3} : Finset ℕ) at hn
      simp only [Finset.mem_insert,Finset.mem_singleton] at hn
      omega
    · rw [hz.2.2,Real.sinh_arsinh]
      linarith [P2.u_lower_positive z hm]
    · intro c
      rw [hz.2.2,Real.sinh_arsinh,hz.2.1]
      exact P2.dualPolynomial_nonneg hm c
  by_cases hW : Real.cosh t≤GW
  · have hg:=Real.one_le_cosh t
    let W:=weights23 (spiralWeight (Real.cosh t)) (spiralWeight_mem hg hW).1
      (spiralWeight_mem hg hW).2
    have h₁ : G1≤Real.cosh t:=(le_of_not_ge hG)
    have hu : 0≤1-1/(2*Real.cosh t):=by
      have hh : 1/(2*Real.cosh t)≤1:=(div_le_one (by positivity)).mpr (by linarith)
      linarith
    refine ⟨W,?_,?_,?_⟩
    · intro n hn
      change n∈({2,3} : Finset ℕ) at hn
      simp only [Finset.mem_insert,Finset.mem_singleton] at hn
      omega
    · rw [spiral_optimal h₁ hW,Real.sinh_arsinh]
      exact hu
    · intro c
      rw [spiral_optimal h₁ hW,Real.sinh_arsinh]
      have hn : dualSymbol W (1-1/(2*Real.cosh t)) (Real.cosh t) c≤0:=by
        change dualSymbol (weights23 _ _ _) _ _ _≤0
        rw [spiralSymbol_factor hg hW]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr (sub_nonneg.mpr (c.property.2.trans hg))) (sq_nonneg _))
            (spiralResidual_nonneg h₁ c)) (by positivity)
      have hgap : 0<Real.cosh t-(c : ℝ):=by linarith [G1_bounds.1,c.property.2]
      rw [dualPolynomial_factor W _ hg] at hn
      nlinarith
  · have ht : GW<Real.cosh t:=lt_of_not_ge hW
    let z:=1/Real.cosh t
    have hz : z∈Ioc (0 : ℝ) P1.zW:=
      ⟨one_div_pos.mpr (Real.cosh_pos _),
        one_div_le_one_div_of_le (by linarith [GW_bounds.1]) ht.le⟩
    have he : Real.cosh t=1/z:=by simp [z]
    have hp:=P1.continuation_physical hz
    have hc:=P1.regularSystem_contacts (P1.continuation_source
      ⟨hz.1.le,hz.2.trans P1.zW_bounds.2.le⟩)
    refine ⟨P1.weights,?_,Real.sinh_nonneg_iff.mpr (V_nonneg t),?_⟩
    · intro n hn
      change n∈({3} : Finset ℕ) at hn
      have hn':=Finset.mem_singleton.mp hn
      omega
    · intro c
      rw [P1.continuation_optimal hz he,Real.sinh_arsinh,he]
      exact P1.dualPolynomial_nonneg hz.1 (by nlinarith [hz.1,hz.2,P1.zW_bounds.2])
        (by rw [←he]; linarith [GW_bounds.1]) hc.1 hc.2 hp.residual c

/-- Every noncentral exponent has a genuine right derivative with strict slope
bound. At GW the appropriate one-sided source arc depends on the sign of t. -/
theorem exists_noncentral_right_derivative {t : ℝ} (ha : P2.Ga<Real.cosh t) :
    ∃ v' : ℝ,HasDerivWithinAt V v' (Ici t) t ∧ |v'|<1 := by
  by_cases hW : Real.cosh t=GW
  · by_cases ht : 0≤t
    · let z:=1/Real.cosh t
      have hz : z∈Ioc (0 : ℝ) P1.zW:=
        ⟨one_div_pos.mpr (Real.cosh_pos _),
          one_div_le_one_div_of_le (by linarith [GW_bounds.1]) hW.ge⟩
      have he : Real.cosh t=1/z:=by simp [z]
      refine ⟨P1.boundaryDerivative z t,?_,P1.abs_boundaryDerivative_lt_one hz he⟩
      apply (P1.hasDerivWithinAt_V hz he).mono_of_mem_nhdsWithin
      apply Filter.mem_of_superset self_mem_nhdsWithin
      intro s hs
      change GW≤Real.cosh s
      rw [←hW]
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_nonneg ht,abs_of_nonneg (ht.trans hs)]
      exact hs
    · have ht' : t<0:=lt_of_not_ge ht
      refine ⟨spiralBoundaryDerivative t,?_,abs_spiralBoundaryDerivative_lt_one t⟩
      have hm : t∈spiralExponentArc:=by
        change G1≤Real.cosh t ∧ Real.cosh t≤GW
        rw [hW]
        exact ⟨G1_lt_GW.le,le_rfl⟩
      apply (hasDerivWithinAt_V_spiral hm).mono_of_mem_nhdsWithin
      have hn : ∀ᶠ s in 𝓝 t,s<0 ∧ G1<Real.cosh s:=
        (eventually_lt_nhds ht').and
          (Real.continuous_cosh.continuousAt.eventually (lt_mem_nhds (by rw [hW]; exact G1_lt_GW)))
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hs hst
      refine ⟨hs.2.le,?_⟩
      rw [←hW]
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_neg hs.1,abs_of_neg ht']
      change t≤s at hst
      linarith
  · by_cases h₁ : Real.cosh t=G1
    · exact ⟨P2.boundaryDerivative P2.zeta1 t,
        (P2.hasDerivAt_V_at_G1 h₁).hasDerivWithinAt,
        P2.abs_boundaryDerivative_lt_one P2.zeta1_mem (h₁.trans P2.G_zeta1.symm)⟩
    · have hr:=V_regular_outside_central ha h₁ hW
      exact ⟨deriv V t,hr.1.hasDerivAt.hasDerivWithinAt,hr.2⟩

/-- One finite memory preserves the exact rate everywhere strictly outside the
central closed arc, including both noncentral switching points. -/
theorem memory_rate_eq_noncentral {q : ℝ} (hq : 0<q) (hq1 : q<1)
    (ha : P2.Ga<Real.cosh (T q)) :
    ∀ᶠ H : ℕ in atTop,growthRate 0 (2*q) (q^2) H=Real.exp (T q) := by
  obtain ⟨v',hd,hv'⟩:=exists_noncentral_right_derivative ha
  apply memory_rate_eq_of_right_boundary (M:=3) hq hq1 (by omega) hd (abs_lt.mp hv').2
  have hn : ∀ᶠ t in 𝓝 (T q),P2.Ga<Real.cosh t:=
    Real.continuous_cosh.continuousAt.eventually (lt_mem_nhds ha)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with t ht
  exact exists_noncentral_dual ht.le

/-- The actual normalized envelope has an exact exponential prefactor on all
noncentral arcs. No dual, factor or price assumption remains. -/
theorem exists_uniform_prefactor_noncentral {q : ℝ} (hq : 0<q) (hq1 : q<1)
    (ha : P2.Ga<Real.cosh (T q)) :
    ∃ H : ℕ,7≤H ∧ ∃ C : ℝ,0<C ∧ ∀ n : ℕ,
      envelope 0 (2*q) (q^2) H n≤C*Real.exp ((n : ℝ)*T q) := by
  obtain ⟨H,hRate,hH⟩:=((memory_rate_eq_noncentral hq hq1 ha).and (eventually_ge_atTop 7)).exists
  obtain ⟨v',hd,hv'⟩:=exists_noncentral_right_derivative ha
  have heq:=T_sub_log_eq_V hq hq1
  have hVT : 0<V (T q):=by rw [←heq]; exact actual_twist_pos hq hq1
  refine ⟨H,hH,?_⟩
  exact exists_prefactor_of_right_source_germ hq hd (abs_lt.mp hv').2 hVT heq hH hRate.le
    ((eventually_hasPhysicalFactors7_of_cosh_gt_Ga hq ha).filter_mono nhdsWithin_le_nhds)

end polyak.FiniteHorizon
