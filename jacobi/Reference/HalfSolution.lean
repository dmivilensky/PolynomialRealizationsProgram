import jacobi.Reference.CoefficientTransform
import jacobi.Reference.SpectralAnalytic

/-!
Article: jacobi, Theorem 2.1.
The reference solution is entire with values in continuous functions
on the physical half interval. The polynomial energy coefficients and
the already proved spatial majorant handle the frequency branch point.
Thus integration against an arbitrary actual GL row preserves entire
energy dependence, including at the singular spatial endpoint.
Use: its proved entire dependence allows the actual GL row integral to define an entire transformed solution u(t,z).
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The reference solution at complex energy as a continuous physical half-domain function.
Use: its proved entire dependence allows the actual GL row integral to define an entire transformed solution u(t,z).
Article: jacobi, Theorem 2.1.
-/
def halfSolution (a : ℝ) (ha : -1<a) (z : ℂ) : C(Interval,ℂ) :=
  halfWave a ha (Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ)))

/-- The continuous-function reference solution evaluates to the original spatial solution at the actual half-domain coordinate.
Use: the entire function-space construction is identified with the literal original source integral at every spatial point.
Article: jacobi, Proposition 2.2.
Proof: the proved evaluation identity for the original compact-domain wave is exactly the defining square-root representation of the energy solution. -/
theorem halfSolution_apply (a : ℝ) (ha : -1<a) (z : ℂ) (t : Interval) :
    halfSolution a ha z t=solution a z (halfTime t) := by
  rw [halfSolution,halfWave_apply]
  rfl

/-- The actual reference function-space solution has its square-root-free polynomial energy series.
Use: proves analyticity across the genuine energy branch point without assuming differentiability of the chosen square root.
Article: jacobi, Proposition 2.2.
Proof: the true square-root frequency has the prescribed energy square. Its actual series coefficients equal the polynomial energy coefficients at every original index. -/
theorem halfSolution_eq_tsum (a : ℝ) (ha : -1<a) (z : ℂ) :
    halfSolution a ha z=∑' n,energyCoefficient a n z • halfSpatialTerm a ha n := by
  unfold halfSolution halfWave
  apply tsum_congr
  intro n
  rw [energyCoefficient_eq_frequency a (frequency_square _) n]

/-- On every energy disk the actual continuous-function energy series has a summable uniform norm majorant.
Use: establishes true entire dependence under every original GL row integral.
Article: jacobi, Proposition 2.2.
Proof: reuse the proved polynomial energy coefficient domination and
the original geometric spatial norm bound. Their product is the same
summable positive-parameter hypergeometric norm series used for the
actual frequency solution, with a fixed spatial norm factor. -/
theorem halfSolution_majorant (a : ℝ) (ha : -1<a) (z : ℂ) :
    ∃ M:ℕ → ℝ,Summable M ∧ ∀ w∈Metric.ball z 1,∀ n,
      ‖energyCoefficient a n w • halfSpatialTerm a ha n‖≤M n := by
  -- The actual physical spatial terms are reused unchanged from the original reference frequency construction.
  obtain ⟨D,_,hbound⟩ := energyCoefficient_bound a z
  let U := fun n => ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n*(1/2:ℂ)^n‖
  have hU : Summable U := Hypergeometric.summable_norm (by norm_num)
  refine ⟨fun n => U n*‖halfSpatialTerm a ha 0‖,hU.mul_right _,fun w hw n => ?_⟩
  have hh := mul_le_mul (hbound w hw n) (halfSpatialTerm_norm a ha n)
    (norm_nonneg _) (norm_nonneg _)
  rw [norm_smul]
  apply hh.trans_eq
  dsimp [U]
  rw [norm_mul (ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n),norm_pow]
  norm_num
  ring

/-- The original reference solution is entire in energy in the genuine uniform norm on the physical half interval.
Use: the actual continuous integral functional for every GL row and point evaluation preserve entire dependence of the transformed solution u(t,z).
Article: jacobi, Proposition 2.2.
Proof: each true energy coefficient is polynomial and multiplies a
fixed original continuous spatial term. The proved locally uniform
summable norm bound permits the community holomorphic-series theorem.
The exact source series identity identifies that analytic sum with
the original function-space reference solution, including at the branch point. -/
theorem halfSolution_analytic (a : ℝ) (ha : -1<a) (z : ℂ) :
    AnalyticAt ℂ (halfSolution a ha) z := by
  -- Analyticity is proved for the actual source energy series, not inferred from the nonanalytic chosen square root.
  obtain ⟨M,hM,hbound⟩ := halfSolution_majorant a ha z
  have hd := Complex.differentiableOn_tsum_of_summable_norm hM
    (F := fun n w => energyCoefficient a n w • halfSpatialTerm a ha n)
    (fun n w _ => ((energyCoefficient_analytic a n w).smul analyticAt_const).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball (fun n w hw => hbound w hw n)
  have he : (fun w:ℂ => ∑' n,energyCoefficient a n w • halfSpatialTerm a ha n)=halfSolution a ha :=
    funext (fun w => (halfSolution_eq_tsum a ha w).symm)
  rw [he] at hd
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))

end
end jacobi.Reference
