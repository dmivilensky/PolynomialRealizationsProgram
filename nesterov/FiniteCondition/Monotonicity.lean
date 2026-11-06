import nesterov.Rates.Monotonicity
import nesterov.FiniteCondition.Positivity
import nesterov.TwoStep.Phase
import nesterov.Closure.Equality
import nesterov.Duality.Persistence

/-! The convergence domain of a fixed stable tuning is an open upper interval
in the strong convexity parameter. -/
namespace nesterov.FiniteCondition
noncomputable section
open Set Filter Spectral TwoStep
open scoped Topology

variable (q : Momentum.Tuning) {L : ℝ} (hL : 0<L)
  (hstable : q.stepSize*L*(1+2*q.tau)<2*(1+q.beta))

abbrev CurvatureDomain (L : ℝ) := {μ : ℝ // μ∈Ioo 0 L}

def curvaturePair (μ : CurvatureDomain L) : SymbolPair :=
  (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ.val L 0

 theorem continuous_curvature_u : Continuous (fun μ : CurvatureDomain L=>(curvaturePair q μ).u) := by
  change Continuous (fun _ : CurvatureDomain L=>
    StationaryMethod.circlePolynomial (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').queryPolynomial 0)
  exact continuous_const

 theorem continuous_curvature_p : Continuous (fun μ : CurvatureDomain L=>(curvaturePair q μ).p) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  let M := Momentum.method q.beta q.tau q.stepSize q.step_pos.ne'
  have hU : Continuous (fun x : CurvatureDomain L × Frequency=>
      (M.queryPolynomial.map Complex.ofRealHom).eval (polyak.Waves.z 0 (Real.arccos x.2))) := by
    unfold polyak.Waves.z
    fun_prop
  have hV : Continuous (fun x : CurvatureDomain L × Frequency=>
      (M.recurrencePolynomial.map Complex.ofRealHom).eval (polyak.Waves.z 0 (Real.arccos x.2))) := by
    unfold polyak.Waves.z
    fun_prop
  have hd : ∀ x : CurvatureDomain L × Frequency,L-x.1.val≠0 := fun x=>
    (sub_pos.mpr x.1.property.2).ne'
  have hA : Continuous (fun x : CurvatureDomain L × Frequency=>((L+x.1.val)/(L-x.1.val):ℝ)) := by
    apply Continuous.div (by fun_prop) (by fun_prop) hd
  have hB : Continuous (fun x : CurvatureDomain L × Frequency=>(2/(L-x.1.val):ℝ)) := by
    apply Continuous.div continuous_const (by fun_prop) hd
  have hh := ((Complex.continuous_ofReal.comp hA).mul hU).sub
    ((Complex.continuous_ofReal.comp hB).mul hV)
  convert hh using 1
  funext x
  exact M.normalizedPolynomial_complex_eval x.1.val L _

 include hstable in
 theorem convergence_isOpen : IsOpen {μ : CurvatureDomain L |
    Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ.val L<1} := by
  rw [isOpen_iff_mem_nhds]
  intro μ hμ
  change Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ.val L<1 at hμ
  have hs : q.Stable μ.val L := (q.stable_iff μ.property.1 μ.property.2).mpr hstable
  have hm := Phase.middleRadius_lt_one_of_stable q μ.property.1 μ.property.2 hs
  have hmid : IQC.middleRadius (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ.val L<Real.exp 0 := by simpa using hm
  obtain ⟨cert⟩ := (Closure.certificate_iff_rate_lt _ μ.property.1 μ.property.2 hmid).mpr (by simpa only [Momentum.momentumRate,Real.exp_zero] using hμ)
  have hp := cert.eventually (m:=curvaturePair q) (t:=fun _ : CurvatureDomain L=>(0:ℝ))
    (continuous_curvature_u q) (continuous_curvature_p q) continuous_const
  filter_upwards [hp] with μ' hμ'
  obtain ⟨cert',_⟩ := hμ'
  have hs' : q.Stable μ'.val L := (q.stable_iff μ'.property.1 μ'.property.2).mpr hstable
  have hm' := Phase.middleRadius_lt_one_of_stable q μ'.property.1 μ'.property.2 hs'
  have hr := IQC.one_exponent μ'.property.1 μ'.property.2 (by simpa using hm') cert'
  simpa only [Momentum.momentumRate,Real.exp_zero] using hr

 def convergenceSet : Set ℝ := {μ | 0<μ ∧ μ<L ∧
    Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L<1}

 include hstable in
 theorem convergenceSet_isOpen : IsOpen (convergenceSet q (L:=L)) := by
  have hh := (isOpen_Ioo : IsOpen (Ioo (0:ℝ) L)).isOpenMap_subtype_val _
    (convergence_isOpen q hstable)
  convert hh using 1
  ext μ
  simp only [convergenceSet,mem_ofPred_eq,mem_image]
  constructor
  · rintro ⟨hμ,hμL,hr⟩
    exact ⟨⟨μ,hμ,hμL⟩,hr,rfl⟩
  · rintro ⟨μ',hr,rfl⟩
    exact ⟨μ'.property.1,μ'.property.2,hr⟩

 include hL hstable in
 theorem convergenceSet_nonempty : (convergenceSet q (L:=L)).Nonempty := by
  have hy : 0<q.stepSize*L := mul_pos q.step_pos hL
  have hmax : q.stepSize*L<maxStep q.beta q.tau :=
    (lt_div_iff₀ (by linarith [q.tau_nonneg] : 0<1+2*q.tau)).mpr hstable
  have hdiag (ξ : ℝ) (hξ : ξ∈Icc (0:ℝ) 2) :
      0<Ltau q.beta q.tau (q.stepSize*L) (q.stepSize*L) ξ :=
    diagonal_pos_of_nonzero hξ (diagonal_nonzero_of_margin q.beta_nonneg q.beta_lt_one q.tau_nonneg hy hmax)
  have hcont : Continuous (fun p : ℝ×ℝ=>Ltau q.beta q.tau (q.stepSize*p.1) (q.stepSize*L) p.2) := by
    unfold Ltau A0 A1 A2
    fun_prop
  have hnear : ∀ᶠ μ in 𝓝 L,∀ ξ∈Icc (0:ℝ) 2,
      0<Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) ξ :=
    isCompact_Icc.eventually_forall_of_forall_eventually (x₀:=L)
      (fun ξ hξ=>hcont.continuousAt.eventually (lt_mem_nhds (hdiag ξ hξ)))
  have hh : ∀ᶠ μ in 𝓝[<] L,μ∈convergenceSet q (L:=L) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,Ioo_mem_nhdsLT hL] with μ hp hμ
    refine ⟨hμ.1,hμ.2,?_⟩
    have hs : q.Stable μ L := (q.stable_iff hμ.1 hμ.2).mpr hstable
    exact positive_Ltau_rate q hμ.1 hμ.2 hs (fun ξ hξ=>hp ξ ⟨hξ.1.le,hξ.2⟩)
  exact hh.exists

 include hL hstable in
/-- A whole interval ending at L has a strict lag-one certificate. -/
 theorem lagOne_interval_near_L : ∃ μstar : ℝ,0<μstar ∧ μstar<L ∧
    ∀ μ∈Ioo μstar L,
      (∀ ξ∈Ioc (0:ℝ) 2,0<Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) ξ) ∧
      μ∈convergenceSet q (L:=L) := by
  have hy : 0<q.stepSize*L := mul_pos q.step_pos hL
  have hmax : q.stepSize*L<maxStep q.beta q.tau :=
    (lt_div_iff₀ (by linarith [q.tau_nonneg] : 0<1+2*q.tau)).mpr hstable
  have hdiag (ξ : ℝ) (hξ : ξ∈Icc (0:ℝ) 2) :
      0<Ltau q.beta q.tau (q.stepSize*L) (q.stepSize*L) ξ :=
    diagonal_pos_of_nonzero hξ (diagonal_nonzero_of_margin q.beta_nonneg q.beta_lt_one q.tau_nonneg hy hmax)
  have hcont : Continuous (fun p : ℝ×ℝ=>Ltau q.beta q.tau (q.stepSize*p.1) (q.stepSize*L) p.2) := by
    unfold Ltau A0 A1 A2
    fun_prop
  have hnear : ∀ᶠ μ in 𝓝 L,∀ ξ∈Icc (0:ℝ) 2,
      0<Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) ξ :=
    isCompact_Icc.eventually_forall_of_forall_eventually (x₀:=L)
      (fun ξ hξ=>hcont.continuousAt.eventually (lt_mem_nhds (hdiag ξ hξ)))
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let μstar := max (L/2) (L-δ/2)
  have hstar : 0<μstar := (by linarith : (0:ℝ)<L/2).trans_le (le_max_left _ _)
  have hstarL : μstar<L := max_lt (by linarith) (by linarith)
  refine ⟨μstar,hstar,hstarL,fun μ hμ=>?_⟩
  have hμ0 := hstar.trans hμ.1
  have hp : ∀ ξ∈Icc (0:ℝ) 2,0<Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) ξ := by
    apply hball
    rw [Real.dist_eq,abs_of_neg (sub_neg.mpr hμ.2)]
    have hh := (le_max_right (L/2) (L-δ/2)).trans_lt hμ.1
    linarith
  have hp' := fun ξ (hξ : ξ∈Ioc (0:ℝ) 2)=>hp ξ ⟨hξ.1.le,hξ.2⟩
  exact ⟨hp',hμ0,hμ.2,positive_Ltau_rate q hμ0 hμ.2
    ((q.stable_iff hμ0 hμ.2).mpr hstable) hp'⟩

 include hL hstable in
/-- Proposition 8.3: the complete actual convergence domain is one open interval. -/
 theorem convergence_interval : ∃ μboundary : ℝ,0≤μboundary ∧ μboundary<L ∧
    convergenceSet q (L:=L)=Ioo μboundary L := by
  let S := convergenceSet q (L:=L)
  have hne : S.Nonempty := convergenceSet_nonempty q hL hstable
  have hbb : BddBelow S := ⟨0,fun μ hμ=>hμ.1.le⟩
  have hopen : IsOpen S := convergenceSet_isOpen q hstable
  refine ⟨sInf S,le_csInf hne (fun μ hμ=>hμ.1.le),?_,?_⟩
  · obtain ⟨μ,hμ⟩ := hne
    exact (csInf_le hbb hμ).trans_lt hμ.2.1
  · ext μ
    constructor
    · intro hμ
      obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hopen μ hμ
      have hleft : μ-δ/2∈S := hball (by
        rw [Metric.mem_ball,Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos (half_pos hδ)]
        linarith)
      exact ⟨(csInf_le hbb hleft).trans_lt (by linarith),hμ.2.1⟩
    · rintro ⟨hl,hu⟩
      obtain ⟨μ',hμ',hμ'μ⟩ := exists_lt_of_csInf_lt hne hl
      have hμpos : 0<μ := hμ'.1.trans hμ'μ
      refine ⟨hμpos,hu,?_⟩
      exact (Rates.rate_antitone_mu _ hμ'.1 hμ'μ.le hu).trans_lt hμ'.2.2

end
end nesterov.FiniteCondition