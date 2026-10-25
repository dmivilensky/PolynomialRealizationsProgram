import polyak.FareyPlateau.Ray.ThresholdDefinition

/-! The actual admissible phase floor and removable curvature function
are analytic at every point of [-1,1], including both endpoints and the
contact. Their source endpoint and contact values are consequences. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set Filter
open scoped BigOperators Topology

theorem SourceCertificate.phaseFloor_data {j k : ℕ} {b : ℤ} {D : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1) :
    AnalyticOnNhd ℝ (Symbols.psi C.lag C.weight) (Icc (-1:ℝ) 1) ∧
      Symbols.psi C.lag C.weight (-1)=0 ∧
      Symbols.psi C.lag C.weight 1=
        2*(∑i,C.weight i*(C.lag i:ℝ))/(∑i,C.weight i*(C.lag i:ℝ)^2) ∧
      Symbols.psi C.lag C.weight (Chart.rationalCosine j k)=Chart.rationalHeight j k ∧
      deriv (Symbols.psi C.lag C.weight) (Chart.rationalCosine j k)=1+D := by
  exact ⟨fun c hc=>C.admissible.phaseFloor_analytic c hc,Symbols.psi_neg_one _ _,
    Symbols.psi_one _ _,phaseFloor_edge_contact hj hjk hb C.admissible⟩

theorem SourceCertificate.analytic_R {j k : ℕ} {b : ℤ} {D : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1) :
    AnalyticOnNhd ℝ C.R (Icc (-1:ℝ) 1) := by
  intro c hc
  by_cases he : c=Chart.rationalCosine j k
  · subst c
    apply Symbols.quadraticQuotient_analytic
    have hψ := C.admissible.phaseFloor_analytic (Chart.rationalCosine j k)
      ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
    have hlin : AnalyticAt ℝ
        (fun z : ℝ=>Chart.rationalHeight j k+(1+D)*(z-Chart.rationalCosine j k))
        (Chart.rationalCosine j k) := by fun_prop
    exact hlin.sub hψ
  · have hψ := C.admissible.phaseFloor_analytic c hc
    have hlin : AnalyticAt ℝ
        (fun z : ℝ=>Chart.rationalHeight j k+(1+D)*(z-Chart.rationalCosine j k)) c := by fun_prop
    have hden : AnalyticAt ℝ (fun z : ℝ=>(z-Chart.rationalCosine j k)^2) c := by fun_prop
    have hg := (hlin.sub hψ).div hden (pow_ne_zero 2 (sub_ne_zero.mpr he))
    apply hg.congr
    filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds he] with z hz
    exact (C.off_contact hj hjk hb hz).symm

end polyak.FareyPlateau.Ray
