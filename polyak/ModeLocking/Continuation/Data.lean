import polyak.ModeLocking.Continuation.WeightedResidues

/-! The analytic primal kernels, class masses and slope moments produced
from primary regularity. All finite dual weights are recovered by the explicit
class lift; no continuation or sign conclusion is assumed. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels Filter
open scoped BigOperators Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

structure ContinuationData where
  primalShift : Continuation.Parameters → (ℝ × (Fin D.d → ℝ))
  mass : Continuation.Parameters → (Fin D.d → ℝ)
  moment : Continuation.Parameters → (Fin D.d → ℝ)
  analytic_primalShift : AnalyticAt ℝ primalShift (Continuation.parameters q)
  analytic_mass : AnalyticAt ℝ mass (Continuation.parameters q)
  analytic_moment : AnalyticAt ℝ moment (Continuation.parameters q)
  primalShift_base : primalShift (Continuation.parameters q) = (s, fun i => (D.primal i : ℝ))
  mass_base : mass (Continuation.parameters q) = D.classWeight
  moment_base : moment (Continuation.parameters q) = D.slopeMoment
  equations : ∀ᶠ p in 𝓝 (Continuation.parameters q),
    (D.continuedMatrix primalShift p).mulVec (primalShift p).2 = 0 ∧
    (D.continuedMatrix primalShift p).transpose.mulVec (mass p) = 0 ∧
    (∑ i, (primalShift p).2 i) = 1 ∧
    (∑ r, mass p r) = ∑ r, D.classWeight r ∧
    (D.continuedPinning primalShift p).mulVec (moment p) = D.slopeTarget primalShift mass p ∧
    (∀ i, 0 < (primalShift p).2 i) ∧ ∀ r, 0 < mass p r

theorem continuationData_nonempty : Nonempty D.ContinuationData := by
  obtain ⟨ψ, μ, hψ, hμ, hψbase, hμbase, hker⟩ := D.analytic_kernel_continuation
  obtain ⟨m, hm, hmbase, hmom⟩ := D.analytic_moment_continuation ψ μ hψ hμ hψbase hμbase
  refine ⟨⟨ψ, μ, m, hψ, hμ, hm, hψbase, hμbase, hmbase, ?_⟩⟩
  filter_upwards [hker, hmom] with p hp hmoment
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hmoment, hp.2.2.2.2.1, hp.2.2.2.2.2⟩

namespace ContinuationData
variable {D} (C : D.ContinuationData)

def shift (p : Continuation.Parameters) : ℝ := (C.primalShift p).1
def primal (p : Continuation.Parameters) : Fin D.d → ℝ := (C.primalShift p).2
def weight (p : Continuation.Parameters) : ℤ → ℝ := D.liftedWeights (C.mass p) (C.moment p)

theorem weight_base (n : ℤ) : C.weight (Continuation.parameters q) n = D.dual n := by
  rw [weight, C.mass_base, C.moment_base, D.liftedWeights_base]

theorem analytic_weight (n : ℤ) : AnalyticAt ℝ (fun p => C.weight p n) (Continuation.parameters q) :=
  D.analyticAt_liftedWeights C.mass C.moment C.analytic_mass C.analytic_moment n

theorem weight_pos : ∀ᶠ p in 𝓝 (Continuation.parameters q), ∀ n ∈ D.lags, 0 < C.weight p n :=
  D.liftedWeights_positive_near C.mass C.moment C.analytic_mass C.analytic_moment C.mass_base C.moment_base

theorem weight_sum : ∀ᶠ p in 𝓝 (Continuation.parameters q), (∑ n ∈ D.lags, C.weight p n) = 1 :=
  C.equations.mono fun p hp => D.liftedWeights_sum (C.mass p) (C.moment p) hp.2.2.2.1

theorem symbol_support_zero {q' : Tuning}
    (hp : (D.continuedMatrix C.primalShift (Continuation.parameters q')).transpose.mulVec
      (C.mass (Continuation.parameters q')) = 0) (i : Fin D.d) :
    finiteSymbol q' (C.shift (Continuation.parameters q')) D.lags
      (C.weight (Continuation.parameters q')) (D.atoms i) = 0 := by
  rw [weight, D.lifted_symbol_grid q' (C.shift (Continuation.parameters q'))
    (C.mass _) (C.moment _) (D.atoms i) (D.atoms_grid i)]
  have he := congrFun hp i
  change (∑ r, Continuation.ambientLag (D.reps r) (D.atoms i)
    (Continuation.sourcePoint q' (C.shift (Continuation.parameters q'))) * C.mass (Continuation.parameters q') r) = 0 at he
  simpa only [Continuation.ambientLag_actual, mul_comm] using he

theorem symbol_support_slope_zero {q' : Tuning}
    (hp : (D.continuedPinning C.primalShift (Continuation.parameters q')).mulVec
      (C.moment (Continuation.parameters q')) = D.slopeTarget C.primalShift C.mass (Continuation.parameters q'))
    (i : Fin D.d) :
    deriv (finiteSymbol q' (C.shift (Continuation.parameters q')) D.lags
      (C.weight (Continuation.parameters q'))) (D.atoms i : ℝ) = 0 := by
  let p := Continuation.parameters q'
  let t := C.shift p
  have hpoint : D.continuedPoint C.primalShift (D.atoms i) p =
      ![q'.kappa, q'.y, q'.beta, t, (D.atoms i : ℝ)] := rfl
  have hslope (n : ℤ) : Continuation.jointSlope n
      (D.continuedPoint C.primalShift (D.atoms i) p) = deriv (lagExtension q' t n) (D.atoms i) := by
    rw [hpoint]
    exact Continuation.jointSlope_actual q' t n (D.atoms i).property
  have hphase : Geometry.jointAngle (D.continuedPoint C.primalShift (D.atoms i) p) =
      Geometry.shiftedCurve q' t (D.atoms i) := by
    rw [hpoint, Geometry.jointAngle_actual q' t (D.atoms i).property]
    rfl
  have he := congrFun hp i
  change (∑ r, (L : ℝ) * Real.sin ((D.reps r : ℝ) * (D.atoms i : ℝ) -
      Geometry.jointAngle (D.continuedPoint C.primalShift (D.atoms i) p)) * C.moment p r) =
    -(∑ r, C.mass p r * Continuation.jointSlope (D.reps r)
      (D.continuedPoint C.primalShift (D.atoms i) p)) -
    ∑ n ∈ D.lags, if n % (L : ℤ) = 0 then D.dual n * Continuation.jointSlope n
      (D.continuedPoint C.primalShift (D.atoms i) p) else 0 at he
  simp_rw [hslope, hphase] at he
  change deriv (finiteSymbol q' t D.lags (D.liftedWeights (C.mass p) (C.moment p))) (D.atoms i : ℝ) = 0
  rw [D.lifted_slope_grid q' t (C.mass p) (C.moment p) i, he]
  ring

end ContinuationData
end polyak.ModeLocking.RegularData
