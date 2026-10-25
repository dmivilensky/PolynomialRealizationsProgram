import polyak.Dynamics.Rate
import Mathlib.Analysis.InnerProductSpace.Spectrum
import polyak.General.QuadraticFunction

/-! Actual finite-dimensional quadratic objectives, including arbitrary
orthogonal coordinates, translated minimizers and additive constants.
The quadratic execution rate uses the original from-rest gradient executor. -/
noncomputable section
namespace polyak.General
open Filter Set
open scoped Topology

structure QuadraticModel (μ L : ℝ) (d : ℕ) where
  H : EuclideanSpace ℝ (Fin d)→ₗ[ℝ]EuclideanSpace ℝ (Fin d)
  symmetric : H.IsSymmetric
  lower : ∀ v,μ*‖v‖^2≤ inner ℝ (H v) v
  upper : ∀ v,inner ℝ (H v) v≤L*‖v‖^2
  center : EuclideanSpace ℝ (Fin d)
  constant : ℝ

namespace QuadraticModel
variable {μ L : ℝ} {d : ℕ} (Q : QuadraticModel μ L d)

def potential : EuclideanSpace ℝ (Fin d)→ℝ :=
  quadraticPotential Q.H Q.center Q.constant

@[simp] theorem gradient_potential (x : EuclideanSpace ℝ (Fin d)) :
    gradient Q.potential x=Q.H (x-Q.center) :=
  gradient_quadraticPotential Q.H Q.symmetric Q.center Q.constant x

theorem admissible (hμ : 0<μ) (hL : μ<L) : SmoothStronglyConvex μ L Q.potential :=
  quadraticPotential_smoothStronglyConvex Q.H Q.symmetric hμ hL Q.lower Q.upper Q.center Q.constant

theorem center_minimizer (hμ : 0≤μ) (x : EuclideanSpace ℝ (Fin d)) :
    Q.potential Q.center≤Q.potential x :=
  quadraticPotential_minimizer Q.H hμ Q.lower Q.center Q.constant x

/-- The model is an ordinary affine quadratic with its actual linear term
and additive constant; centering is a representation, not a restriction. -/
theorem potential_affine (x : EuclideanSpace ℝ (Fin d)) :
    Q.potential x=(1/2:ℝ)*inner ℝ (Q.H x) x+inner ℝ (-Q.H Q.center) x+
      (Q.constant+(1/2:ℝ)*inner ℝ (Q.H Q.center) Q.center) := by
  unfold potential quadraticPotential
  simp only [map_sub,inner_sub_left,inner_sub_right,inner_neg_left]
  rw [Q.symmetric x Q.center,real_inner_comm x (Q.H Q.center)]
  ring

end QuadraticModel

/-- Every affine SPD quadratic with the source curvature bounds is
represented in the execution class, including every linear term. -/
theorem affineQuadratic_eq_model {μ L : ℝ} (hμ : 0<μ) {d : ℕ}
    (H : EuclideanSpace ℝ (Fin d)→ₗ[ℝ]EuclideanSpace ℝ (Fin d)) (hH : H.IsSymmetric)
    (hlower : ∀ v,μ*‖v‖^2≤ inner ℝ (H v) v)
    (hupper : ∀ v,inner ℝ (H v) v≤L*‖v‖^2)
    (b : EuclideanSpace ℝ (Fin d)) (c : ℝ) :
    ∃ Q : QuadraticModel μ L d,∀ x,
      (1/2:ℝ)*inner ℝ (H x) x+inner ℝ b x+c=Q.potential x := by
  obtain ⟨a,c',he⟩:=affine_quadratic_representation H hH hμ hlower b c
  exact ⟨⟨H,hH,hlower,hupper,a,c'⟩,he⟩

/-- All ratios of actual shifted quadratic gradient executions in every
positive finite dimension. -/
def quadraticRatios (μ L α β : ℝ) (N : ℕ) : Set ℝ :=
  {r | ∃ (d : ℕ),0<d ∧ ∃ (Q : QuadraticModel μ L d)
    (x₀ : EuclideanSpace ℝ (Fin d)),x₀≠Q.center ∧
      r=‖Dynamics.iterate (gradient Q.potential) α β x₀ N-Q.center‖/‖x₀-Q.center‖}

def quadraticWorst (μ L α β : ℝ) (N : ℕ) : ℝ :=
  sSup (insert 0 (quadraticRatios μ L α β N))

def quadraticExecutionRate (μ L α β : ℝ) : ℝ :=
  limsup (fun N : ℕ=>quadraticWorst μ L α β N^((N:ℝ)⁻¹)) atTop

end polyak.General
