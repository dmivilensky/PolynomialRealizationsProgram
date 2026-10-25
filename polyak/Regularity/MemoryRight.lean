import polyak.Regularity.Memory
import polyak.Regularity.RightExtension

/-!
Article: Appendix C, finite memory at shared endpoints of the source arcs.
Use: only the right-hand source germ above the optimal exponent is required.
The actual boundary need not have an ordinary derivative across a switch.
-/
noncomputable section
namespace polyak.Regularity
open Growth Spectral Boundary Set Filter
open scoped Topology

theorem memory_rate_eq_of_eventual_right_certificates {q : ℝ} {M : ℕ}
    (hq : 0<q)
    (hc : ∀ᶠ t in 𝓝[>] (T q),
      ∃ cert : Duality.StrictCertificate (Waves.multiplierMap 0 (2*q) (q^2) t) t,
        ∀ n∈cert.lags,n≤M) :
    ∀ᶠ H : ℕ in atTop,
      Growth.FiniteHorizon.growthRate 0 (2*q) (q^2) H=Real.exp (T q) := by
  have hh : ∀ᶠ t in 𝓝 (T q),T q<t →
      ∃ cert : Duality.StrictCertificate (Waves.multiplierMap 0 (2*q) (q^2) t) t,
        ∀ n∈cert.lags,n≤M := eventually_nhdsWithin_iff.mp hc
  obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hh
  have hlog : Real.log (Growth.growthRate 0 (2*q) (q^2))=T q :=
    (T_eq_log_freeRate hq).symm
  have hm := Growth.FiniteHorizon.eventually_growthRate_eq_of_certificates
    (H₀:=M) (by positivity : (2*q : ℝ)≠0) (sub_pos.mpr hab.2) (by
      intro t hlt hhi
      rw [hlog] at hlt hhi
      exact hsub ⟨hab.1.trans hlt,by linarith⟩ hlt)
  have heq : Growth.growthRate 0 (2*q) (q^2)=Real.exp (T q) := freeRate_eq_exp_T hq
  simpa only [heq] using hm

theorem memory_rate_eq_of_right_boundary {q v' : ℝ} {M : ℕ}
    (hq : 0<q) (hq1 : q<1) (hM : 1≤M)
    (hd : HasDerivWithinAt V v' (Ici (T q)) (T q)) (hv' : v'<1)
    (hduals : ∀ᶠ t in 𝓝[>] (T q),∃ W : DualWeights,
      (∀ n∈W.lags,n≤M) ∧ 0≤Real.sinh (V t) ∧
      ∀ c : Frequency,0≤(dualPolynomial W (Real.sinh (V t)) (Real.cosh t)).eval (c : ℝ)) :
    ∀ᶠ H : ℕ in atTop,
      Growth.FiniteHorizon.growthRate 0 (2*q) (q^2) H=Real.exp (T q) := by
  let g := rightExtension V v' (T q)
  let F : ℝ → ℝ := fun t => t-Real.log q-g t
  have hF : F (T q)=0 := by
    dsimp [F,g]
    rw [rightExtension_eq le_rfl]
    linarith [T_sub_log_eq_V hq hq1]
  have hD : HasDerivAt F (1-v') (T q) :=
    ((hasDerivAt_id _).sub_const _).sub (rightExtension_hasDerivAt hd)
  have hsl : ∀ᶠ t in 𝓝[>] (T q),0<slope F (T q) t :=
    (hD.tendsto_slope.mono_left (nhdsGT_le_nhdsNE _)).eventually
      (lt_mem_nhds (by linarith : (0 : ℝ)<1-v'))
  apply memory_rate_eq_of_eventual_right_certificates hq
  filter_upwards [hsl,hduals,self_mem_nhdsWithin] with t ht hdW hgt
  obtain ⟨W,hW,hu,hQ⟩ := hdW
  rw [slope_def_field,hF,sub_zero] at ht
  have hpos : 0<F t := by
    have hgt' : T q<t := hgt
    rcases div_pos_iff.mp ht with hh|hh <;> linarith
  have hgap : V t<t-Real.log q := by
    dsimp [F,g] at hpos
    rw [rightExtension_eq hgt.le] at hpos
    linarith
  have hex := strictCertificate_above_retains_lags W t hu
    (Real.sinh_lt_sinh.mpr hgap) hQ
  rw [Real.arsinh_sinh] at hex
  obtain ⟨cert,hcert⟩ := hex
  rw [Waves.multiplierMap_polyak q t hq]
  refine ⟨cert,?_⟩
  intro n hn
  rw [hcert] at hn
  rcases Finset.mem_insert.mp hn with rfl|hn
  · exact hM
  · exact hW n hn

end polyak.Regularity
