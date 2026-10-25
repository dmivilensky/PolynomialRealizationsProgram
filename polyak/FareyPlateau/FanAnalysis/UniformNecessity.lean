import polyak.FareyPlateau.FanAnalysis.CompactGeometry
import polyak.FareyPlateau.FanAnalysis.AmbientUniform
import polyak.FareyPlateau.FanAnalysis.SeparationTests
import polyak.FareyPlateau.FanAnalysis.SourceMass

/-! Compact-uniform necessity for actual measures. Four jointly analytic
negative tests give a common separating neighborhood, and one order cutoff
works for every tuning and both signed fan families. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.CompactFamily.Data
open General Levels ModeLocking Set Filter MeasureTheory
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
variable {j k : ℕ} (B : CompactFamily.Data X j k)

theorem uniform_separating_test {η h ρ : ℝ} (hη : 0<η)
    (hh : h=1 ∨ h= -((k:ℝ)-1)) (hρ : ρ=1 ∨ ρ= -1) :
    ∀ᶠ δ in 𝓝[≠] (0:ℝ),∀x : X,
      Actual.separatingTest (B.adjacent x) (Actual.critical (B.adjacent x)+η) h ρ δ<0 := by
  obtain ⟨r,hr,hstrip⟩ := B.phase_strip
  let F : Parameters.Point×ℝ→ℝ := fun z=>
    -Parameters.separatingTest j k B.lower (B.shiftError η) h ρ z
  have hphase (δ : ℝ) (hδ : |δ|<r) : Real.sin (Parameters.omega j k+h*δ)≠0 := by
    rcases hh with rfl|rfl
    · simpa only [one_mul] using (hstrip δ hδ).1
    · convert (hstrip δ hδ).2 using 1; congr 1; ring
  have hF (x : X) (δ : ℝ) (hδ : |δ|<r) : AnalyticAt ℝ F (B.coordinates x,δ) :=
    (Parameters.analytic_separatingTest (B.analytic_shiftError η) h ρ (B.coordinates x,δ)
      (hphase δ hδ)).neg
  have hbridge (x : X) (δ : ℝ) : F (B.coordinates x,δ)=
      -Actual.separatingTest (B.adjacent x) (Actual.critical (B.adjacent x)+η) h ρ δ := by
    dsimp only [F]
    rw [←B.lower_eq x]
    change -Parameters.separatingTest j k (B.adjacent x).lower (B.shiftError η) h ρ
      (Parameters.coordinates (B.tuning x),δ)=_
    rw [Actual.separatingTest_actual (B.adjacent x)]
    change -Actual.separatingTest (B.adjacent x) (B.shiftError η (B.coordinates x)) h ρ δ=_
    rw [B.shiftError_actual]
  have hlim (x : X) : ∃c : ℝ,0<c ∧
      Tendsto (fun δ=>F (B.coordinates x,δ)/δ^2) (𝓝[≠] 0) (𝓝 c) := by
    refine ⟨2*η*(Real.sin (Real.pi/k))^3,by positivity [Actual.sin_positive (B.adjacent x)],?_⟩
    have he := (Actual.separatingTest_limit (B.adjacent x) η h ρ hh hρ).neg
    convert he using 1
    · ext δ
      rw [hbridge,neg_div]
    · congr 1
      ring
  have he := AmbientUniform.uniform_positive_of_pointwise F B.coordinates B.continuous_coordinates hr hF hlim
  filter_upwards [he] with δ hδ x
  have hx := hδ x
  rw [hbridge] at hx
  exact neg_pos.mp hx

theorem uniform_infeasible_lags {η : ℝ} (hη : 0<η) :
    ∀ᶠ δ in 𝓝[≠] (0:ℝ),∀x : X,∀P : Fan.Data,P.j=j → P.k=k → P.delta=δ →
      ∀wa wc : ℝ,0≤wa → 0≤wc → 0<wa+wc →
        ¬∀n : ℤ,0≤Actual.pairLag (B.adjacent x) P (Actual.critical (B.adjacent x)+η) δ wa wc n := by
  have h11 := B.uniform_separating_test hη (Or.inl rfl) (Or.inl rfl)
  have h1m := B.uniform_separating_test hη (Or.inl rfl) (Or.inr rfl)
  have hm1 := B.uniform_separating_test hη (Or.inr rfl) (Or.inl rfl)
  have hmm := B.uniform_separating_test hη (Or.inr rfl) (Or.inr rfl)
  filter_upwards [h11,h1m,hm1,hmm] with δ h11δ h1mδ hm1δ hmmδ x P hj hk hPd wa wc hwa hwc hsum hfeas
  let A := B.adjacent x
  let e := Actual.critical A+η
  have hdual := Actual.dual_constraint A P hj hk hPd hfeas
  by_cases hsign : 0≤Actual.separatingCorrection A*δ
  · have horigin := Actual.origin_constraint A P hk hPd hfeas 1
    have hn := negative_weighted_sum (h11δ x) (hm1δ x) hwa hwc hsum
    have hmul := mul_nonneg hsign horigin
    simp only [Actual.separatingTest,one_mul,mul_one] at hn
    simp only [Int.cast_one,one_mul] at hmul
    dsimp only [A,Actual.nearAngle,Actual.farAngle] at hdual hmul
    nlinarith only [hn,hdual,hmul]
  · have horigin := Actual.origin_constraint A P hk hPd hfeas (-1)
    have hn := negative_weighted_sum (h1mδ x) (hmmδ x) hwa hwc hsum
    have hmul := mul_nonneg (neg_nonneg.mpr (le_of_not_ge hsign)) horigin
    simp only [Actual.separatingTest,one_mul,mul_one,neg_mul,mul_neg,neg_neg] at hn
    simp only [Int.cast_neg,Int.cast_one,mul_neg,neg_neg,neg_mul,one_mul] at hmul
    dsimp only [A,Actual.nearAngle,Actual.farAngle] at hdual hmul
    nlinarith only [hn,hdual,hmul]

theorem uniform_no_measure_small {η : ℝ} (hη : 0<η) :
    ∀ᶠ δ in 𝓝[≠] (0:ℝ),∀x : X,∀P : Fan.Data,P.j=j → P.k=k → P.delta=δ →
      ∀a c : Frequency,(a:ℝ)=P.near → (c:ℝ)=P.far →
        ¬∃μ : Measure Frequency,ProgramSolution
          (Geometry.shiftedCurve (B.tuning x) ((B.adjacent x).edgeShift-(Actual.critical (B.adjacent x)+η)*δ^2))
          nonzeroLags μ ∧ (∀ᵐ ω ∂μ,ω=a ∨ ω=c) := by
  filter_upwards [B.uniform_infeasible_lags hη,
    (B.uniform_angle_actual η 1).filter_mono nhdsWithin_le_nhds,
    (B.uniform_angle_actual η (-((k:ℝ)-1))).filter_mono nhdsWithin_le_nhds]
    with δ hsep hanglea hanglec x P hj hk hPd a c ha hc hμ
  let A := B.adjacent x
  let e := Actual.critical A+η
  have hcenter : P.center=(A.frequency:ℝ) := by
    change 2*Real.pi*P.j/P.k=2*Real.pi*j/k
    rw [hj,hk]
    push_cast
    rfl
  have hnear : P.near=(A.frequency:ℝ)+δ := by
    have hh := P.near_displacement
    rw [hcenter,hPd] at hh
    linarith
  have hfar : P.far=(A.frequency:ℝ)-((k:ℝ)-1)*δ := by
    have hh := P.far_displacement
    rw [hcenter,hPd,hk] at hh
    simpa only [Int.cast_natCast] using hh
  have hca : Geometry.shiftedCurve (B.tuning x) (A.edgeShift-e*δ^2) a=Actual.nearAngle A e δ := by
    change Geometry.shiftedAngle (B.tuning x) _ (a:ℝ)=_
    rw [ha,hnear]
    symm
    have hh := hanglea x
    rw [B.angle_actual] at hh
    simpa only [one_mul,Actual.nearAngle] using hh
  have hcc : Geometry.shiftedCurve (B.tuning x) (A.edgeShift-e*δ^2) c=Actual.farAngle A e δ := by
    change Geometry.shiftedAngle (B.tuning x) _ (c:ℝ)=_
    rw [hc,hfar]
    change Geometry.shiftedAngle (B.tuning x) _ ((A.frequency:ℝ)-((k:ℝ)-1)*δ)=
      anglePath (B.tuning x) A.edgeShift A.frequency (-((k:ℝ)-1)) e δ
    have hh := hanglec x
    rw [B.angle_actual] at hh
    convert hh.symm using 1; congr 1; ring
  dsimp only [A,e] at hca hcc
  obtain ⟨μ,hprog,hcar⟩ := hμ
  have hm := pair_solution_inequalities (pair_frequency_ne P ha hc) hcar hprog
  have hsum : 0<(pairWeight μ a c 0:ℝ)+(pairWeight μ a c 1:ℝ) := by
    have hh := hm.1
    simp only [Fin.sum_univ_two] at hh
    exact_mod_cast hh
  apply hsep x P hj hk hPd _ _ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) hsum
  intro n
  simpa only [Curve.lag,hca,hcc,ha,hc,Actual.pairLag] using hm.2.2 n

theorem uniform_no_measure {η : ℝ} (hη : 0<η) :
    ∃L₀ : ℕ,∀x : X,∀P : Fan.Data,P.j=j → P.k=k → (L₀:ℤ)≤P.L →
      ∀a c : Frequency,(a:ℝ)=P.near → (c:ℝ)=P.far →
        ¬∃μ : Measure Frequency,ProgramSolution
          (Geometry.shiftedCurve (B.tuning x) ((B.adjacent x).edgeShift-(Actual.critical (B.adjacent x)+η)*P.delta^2))
          nonzeroLags μ ∧ (∀ᵐ ω ∂μ,ω=a ∨ ω=c) := by
  let x₀ := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨L₀,hL₀⟩ := large_order_small_delta (B.adjacent x₀).period_ge (B.uniform_no_measure_small hη)
  exact ⟨L₀,fun x P hj hk hPL=>hL₀ P hk hPL x P hj hk rfl⟩

end polyak.FareyPlateau.FanAnalysis.CompactFamily.Data
