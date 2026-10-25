import polyak.Growth.HorizonRate
import polyak.Regularity.Critical
import polyak.Boundary.P2.Results
import polyak.Boundary.P2.Derivative
import polyak.Boundary.SpiralRegularity
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Article: Appendix C, finite memory retains the exact Polyak growth rate.
Use: source dual weights keep a uniformly bounded lag support. Their actual
strict certificates above the boundary contradict the proved H-class plateau.
The concrete results below discharge the source and slope inputs on actual arcs.
-/
noncomputable section
namespace polyak.Boundary
open Spectral

/-- The constructive strict certificate preserves the actual selected lag support. -/
theorem strictCertificate_above_retains_lags (W : DualWeights) (t : ℝ) {u u' : ℝ} (hu : 0 ≤ u)
    (huu' : u < u')
    (hQ : ∀ c : Frequency, 0 ≤ (dualPolynomial W u (Real.cosh t)).eval (c : ℝ)) :
    ∃ cert : Duality.StrictCertificate (Waves.polyakMultiplier (Real.arsinh u')) t,
      cert.lags=insert 1 W.lags := by
  have hG := Real.one_le_cosh t
  have hup : 0 < u' := hu.trans_lt huu'
  have hdiff : 0 < u'^2-u^2 := by nlinarith
  have hmono (c : Frequency) :
      dualSymbol W u' (Real.cosh t) c ≤ -(Real.cosh t-c)*(u'^2-u^2) := by
    have hm := dualSymbol_mono W hG hu huu'.le c
    have hn := dualSymbol_nonpos_of_polynomial W u hG hQ c
    linarith
  by_cases hGt : 1 < Real.cosh t
  · refine ⟨strictCertificateOfWeights W (Real.arsinh u') t 0
      ((Real.cosh t-1)*(u'^2-u^2)) le_rfl (mul_pos (by linarith) hdiff) ?_,rfl⟩
    intro c
    simp only [Real.sinh_arsinh,mul_zero,zero_mul,add_zero]
    have hc : 0 ≤ 1-(c : ℝ) := by linarith [c.property.2]
    have hprod := mul_nonneg hc hdiff.le
    nlinarith [hmono c]
  · have hG1 : Real.cosh t=1 := le_antisymm (le_of_not_gt hGt) hG
    let γ := (u'^2-u^2)/8
    have hγ : 0 < γ := by dsimp [γ]; positivity
    refine ⟨strictCertificateOfWeights W (Real.arsinh u') t γ (2*γ*u'^2) hγ.le (by positivity) ?_,rfl⟩
    intro c
    simp only [Real.sinh_arsinh]
    have hbase := hmono c
    rw [hG1] at hbase
    have hc : 0 ≤ 1-(c : ℝ) := by linarith [c.property.2]
    have hg : g u' c ≤ 2*(1-(c : ℝ))-u'^2 := by
      unfold g
      nlinarith [sq_nonneg ((c : ℝ)-1)]
    have hgm := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*γ by positivity)
    have hrem : 0 ≤ (1-(c : ℝ))*(u'^2-u^2-4*γ) := by
      apply mul_nonneg hc
      dsimp [γ]
      linarith
    rw [hG1]
    nlinarith [hgm,hrem]

end polyak.Boundary

namespace polyak.Regularity
open Growth Spectral Boundary Set Filter
open scoped Topology

/-- A positive boundary slope gap gives actual strict feasibility failure immediately
above the exponent, with the source's uniform finite lag support. -/
theorem memory_rate_eq_of_boundary {q v' : ℝ} {H₀ : ℕ}
    (hq : 0<q) (hq1 : q<1) (hH₀ : 1 ≤ H₀)
    (hd : HasDerivAt V v' (T q)) (hv' : v'<1)
    (hduals : ∀ᶠ t in 𝓝 (T q), ∃ W : DualWeights,
      (∀ n∈W.lags,n ≤ H₀) ∧ 0 ≤ Real.sinh (V t) ∧
      ∀ c : Frequency,0 ≤ (dualPolynomial W (Real.sinh (V t)) (Real.cosh t)).eval (c : ℝ)) :
    ∀ᶠ H : ℕ in atTop,
      Growth.FiniteHorizon.growthRate 0 (2*q) (q^2) H=Real.exp (T q) := by
  let F : ℝ → ℝ := fun t => t-Real.log q-V t
  have hF : F (T q)=0 := by dsimp [F]; linarith [T_sub_log_eq_V hq hq1]
  have hD : HasDerivAt F (1-v') (T q) := ((hasDerivAt_id _).sub_const _).sub hd
  have hsl : ∀ᶠ t in 𝓝[≠] (T q),0<slope F (T q) t :=
    hD.tendsto_slope.eventually (lt_mem_nhds (by linarith : (0 : ℝ)<1-v'))
  have hright : ∀ᶠ t in 𝓝 (T q),T q<t → V t<t-Real.log q := by
    filter_upwards [eventually_nhdsWithin_iff.mp hsl] with t ht hgt
    have hpos := ht (by simpa using (ne_of_gt hgt))
    rw [slope_def_field,hF,sub_zero] at hpos
    have hh := (div_pos_iff.mp hpos)
    have hFpos : 0<F t := by rcases hh with hh|hh <;> linarith
    dsimp only [F] at hFpos
    linarith
  obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hright.and hduals)
  have hlog : Real.log (Growth.growthRate 0 (2*q) (q^2))=T q :=
    (Spectral.T_eq_log_freeRate hq).symm
  have hmem := Growth.FiniteHorizon.eventually_growthRate_eq_of_certificates
    (H₀:=H₀) (by positivity : (2*q : ℝ)≠0) (sub_pos.mpr hab.2) (by
      intro t hlt hhi
      rw [hlog] at hlt hhi
      have ht : t∈Ioo a b := ⟨hab.1.trans hlt,by linarith⟩
      obtain ⟨hr,W,hW,hu,hQ⟩ := hsub ht
      have hdiff : Real.sinh (V t)<Real.sinh (t-Real.log q) :=
        Real.sinh_lt_sinh.mpr (hr hlt)
      have hex := strictCertificate_above_retains_lags W t hu hdiff hQ
      rw [Real.arsinh_sinh] at hex
      obtain ⟨cert,hcert⟩ := hex
      rw [Waves.multiplierMap_polyak q t hq]
      refine ⟨cert,?_⟩
      intro n hn
      rw [hcert] at hn
      rcases Finset.mem_insert.mp hn with rfl|hn
      · exact hH₀
      · exact hW n hn)
  have heq : Growth.growthRate 0 (2*q) (q^2)=Real.exp (T q) :=
    Spectral.freeRate_eq_exp_T hq
  simpa only [heq] using hmem


/-- The complete open rational P₂ arc has exactly the original rate with finite memory. -/
theorem memory_rate_eq_p2 {q z : ℝ} (hq : 0<q) (hq1 : q<1)
    (hz : z∈Ioo P2.zeta1 P2.zetaA) (ht : Real.cosh (T q)=P2.G z) :
    ∀ᶠ H : ℕ in atTop,
      Growth.FiniteHorizon.growthRate 0 (2*q) (q^2) H=Real.exp (T q) := by
  have hzm:=P2.arc_mem_interval ⟨hz.1.le,hz.2.le⟩
  apply memory_rate_eq_of_boundary (H₀:=3) hq hq1 (by omega)
    (P2.hasDerivAt_V hz ht) (abs_lt.mp (P2.abs_boundaryDerivative_lt_one hzm ht)).2
  have hlo : P2.Ga<Real.cosh (T q) := by
    rw [ht]
    exact P2.G_strictAntiOn hzm P2.zetaA_mem hz.2
  have hhi : Real.cosh (T q)<Boundary.G1 := by
    rw [ht,←P2.G_zeta1]
    exact P2.G_strictAntiOn P2.zeta1_mem hzm hz.1
  have hn : ∀ᶠ t in 𝓝 (T q),P2.Ga<Real.cosh t ∧ Real.cosh t<Boundary.G1 :=
    ((isOpen_lt continuous_const Real.continuous_cosh).inter
      (isOpen_lt Real.continuous_cosh continuous_const)).mem_nhds ⟨hlo,hhi⟩
  filter_upwards [hn] with t ht
  obtain ⟨z,hz,_⟩:=P2.p2_arc ⟨ht.1.le,ht.2.le⟩
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

/-- The complete open exact spiral arc has exactly the original rate with finite memory. -/
theorem memory_rate_eq_spiral {q : ℝ} (hq : 0<q) (hq1 : q<1)
    (hl : Boundary.G1<Real.cosh (T q)) (hu : Real.cosh (T q)<GW) :
    ∀ᶠ H : ℕ in atTop,
      Growth.FiniteHorizon.growthRate 0 (2*q) (q^2) H=Real.exp (T q) := by
  apply memory_rate_eq_of_boundary (H₀:=3) hq hq1 (by omega)
    (hasDerivAt_V_spiral hl hu) (abs_lt.mp (abs_spiralBoundaryDerivative_lt_one _)).2
  have hn : ∀ᶠ t in 𝓝 (T q),Boundary.G1<Real.cosh t ∧ Real.cosh t<GW :=
    ((isOpen_lt continuous_const Real.continuous_cosh).inter
      (isOpen_lt Real.continuous_cosh continuous_const)).mem_nhds ⟨hl,hu⟩
  filter_upwards [hn] with t ht
  have hg:=Real.one_le_cosh t
  let W:=weights23 (spiralWeight (Real.cosh t)) (spiralWeight_mem hg ht.2.le).1
    (spiralWeight_mem hg ht.2.le).2
  have huv : 0 ≤ 1-1/(2*Real.cosh t) := by
    have hh : 1/(2*Real.cosh t) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  refine ⟨W,?_,?_,?_⟩
  · intro n hn
    change n∈({2,3} : Finset ℕ) at hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    omega
  · rw [spiral_optimal ht.1.le ht.2.le,Real.sinh_arsinh]
    exact huv
  · intro c
    rw [spiral_optimal ht.1.le ht.2.le,Real.sinh_arsinh]
    have hn : dualSymbol W (1-1/(2*Real.cosh t)) (Real.cosh t) c ≤ 0 := by
      change dualSymbol (weights23 _ _ _) _ _ _ ≤ 0
      rw [spiralSymbol_factor hg ht.2.le]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (sub_nonneg.mpr (c.property.2.trans hg))) (sq_nonneg _))
          (spiralResidual_nonneg ht.1.le c)) (by positivity)
    have hgap : 0 < Real.cosh t-(c : ℝ) := by linarith [G1_bounds.1,c.property.2]
    rw [dualPolynomial_factor W _ hg] at hn
    nlinarith


end polyak.Regularity
