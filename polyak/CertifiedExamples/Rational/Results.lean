import polyak.CertifiedExamples.Rational.SmallDenominators
import polyak.CertifiedExamples.Rational.Harmonics
import polyak.Certificates.PartII.Rational.Polynomials
import polyak.Certificates.PartII.Rational.Slacks
import polyak.Farey.Examples.Acceptance

/-! Unconditional source conclusions for the two rational examples in Part II.
Only exact JSON proposals are generated; actual source identities, the reduction
to all signed integer lags and the from-rest trajectory are independent proofs. -/
noncomputable section
namespace polyak.CertifiedExamples.Rational
open polyak.Farey.Examples polyak.Levels MeasureTheory
open polyak.Certificates.PartII.Rational Filter polyak.Dynamics
open scoped Topology

theorem proposition_thirteen :
    Geometry.Gap 4 thirteenTuning ∧
      (∀ω:Frequency,Real.pi/6<thirteenTuning.angle ω) ∧
      (∀ω:Frequency,¬ProgramSolution (tuningCurve thirteenTuning) nonzeroLags (Measure.dirac ω)) ∧
      RawSpectrumSolution thirteenTuning thirteenNu ∧
      ProgramSolution (tuningCurve thirteenTuning) nonzeroLags thirteenW ∧
      polyak.Farey.FanPeriodicOrbit thirteenTuning 13 2 ∧ 1≤thirteenTuning.rate :=
  thirteen_acceptance thirteenFloor thirteen_gap_checks thirteen_small_denominators thirteen_finite_signs

theorem thirteen_all_integer_lags (n:ℤ) : 0≤thirteenRawLag n := by
  rw [thirteen_raw_lag_residue]
  have hn : 0≤n%13 ∧ n%13<13 := ⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩
  by_cases hz:n%13=0
  · rw [hz]
    simpa using thirteen_raw_lag_multiple 0 |>.ge
  · have hval : n%13=((n%13).toNat:ℤ) := (Int.toNat_of_nonneg hn.1).symm
    rw [hval]
    have hpositive : 0<(n%13).toNat := by omega
    have hless : (n%13).toNat<13 := by omega
    have hf : ∀m:ℕ,0<m→m<13→0≤thirteenRawLag m := by
      intro m hm hmk
      have he : ((m-1:ℕ):ℤ)+1=(m:ℤ) := by omega
      simpa only [he] using thirteen_finite_signs.2 ⟨m-1,by omega⟩
    exact hf _ hpositive hless

theorem proposition_thirteen_actual_harmonics :
    ∃f:EuclideanSpace ℝ (Fin 5)→ℝ,
      CenteredSmoothStronglyConvex thirteenTuning.x thirteenTuning.y f ∧
      ∃x₀,x₀≠0 ∧ ∃c₀:ℝ,0<c₀ ∧
      ∃Q:EuclideanSpace ℂ Bool→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 5),
        (∀n,c₀*‖x₀‖≤‖iterate (gradient f) 1 thirteenTuning.beta x₀ n‖) ∧
        Function.Periodic (fun n=>Q (thirteenHarmonics n)) 13 ∧
        Tendsto (fun n=>iterate (gradient f) 1 thirteenTuning.beta x₀ n-
          Q (thirteenHarmonics n)) atTop (𝓝 0) :=
  thirteen_harmonic_startup thirteen_finite_signs

theorem proposition_convergence_gap : Geometry.Gap 4 convergenceTuning ∧
    (∀c∈Set.Icc (-1:ℝ) 1,
      Farey.Certificates.twoLagLeft convergenceTuning 4 (13/100) (1/1000) c<
        Farey.Certificates.twoLagRight 4 (13/100) c) ∧ convergenceTuning.rate<1 := by
  refine ⟨convergence_in_gap_four,?_,convergence_rate_lt_one⟩
  intro c hc
  have h := convergence_positive c hc
  rw [←convergence_sextic_exact] at h
  exact sub_pos.mp h

end polyak.CertifiedExamples.Rational
