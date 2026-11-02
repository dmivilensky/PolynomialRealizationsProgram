import krylov.Functions.PlanarFiniteMinimax
import krylov.Functions.PlanarRFCFModel

/-!
Article: main_krylov, thm:Fplanar, genuine endpoint-only centre rule.
Use: reconstruct the three observed tensor coefficients from the actual
endpoint values and gradients, then execute the sharp centre output without
receiving any unknown tensor or hidden completion. Exact stationary data
perform zero final movement, as required by quadratic CG consistency.
Source: actual cubic trapezoid identities and the proved centre upper bound.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
open scoped InnerProductSpace

/-- The three observed coefficients computed exclusively from actual scalar
values and gradients at the first, middle and last planar samples.
Article: main_krylov, thm:Fplanar. -/
def planeObservedBinaryData (p r f₀ f₁ f₂ : ℝ) (g₀ g₁ g₂ : Plane) : Observation :=
  ⟨-12*(f₁-f₀-(1/2:ℝ)*inner ℝ (g₀+g₁) (planeOfPair (p,0)))/p^3,
    2*(pairOfPlane g₂).1/(r*p^2),
    -12*(f₂-f₁-(1/2:ℝ)*inner ℝ (g₁+g₂) (planeOfPair (0,r*p)))/(r*p)^3⟩

set_option maxHeartbeats 1000000 in
/-- The true cubic endpoint data recover exactly A, B+rC and D.
No hidden coefficient is passed to the observer.
Article: main_krylov, thm:Fplanar, actual information dictionary. -/
theorem planeObservedBinaryData_eq (p r : ℝ) (hp : p≠0) (hr : r≠0)
    (t : krylov.Tensor.BinaryCubic) :
    let f := planeCubicObjective p r t
    let G := gradient f
    planeObservedBinaryData p r (f 0) (f (planeOfPair (p,0))) (f (planeOfPair (p,r*p)))
      (G 0) (G (planeOfPair (p,0))) (G (planeOfPair (p,r*p)))=observe r t := by
  dsimp only
  unfold planeObservedBinaryData observe
  congr 1 <;>
    simp [planeCubicObjective,planarCubicObjective,planarReferenceQuadratic,planarValueFamily,
      planeCubicGradient_actual,planeCubicGradient,planarCubicGradient,planarValueCoordinateDerivative,
      planeOfPair,pairOfPlane,PiLp.inner_apply,Fin.sum_univ_two] <;> field_simp [hp,hr] <;> ring

/-- The sharp final centre computed from actual endpoint samples only.
Zero actual post-search gradient leaves the searched endpoint fixed.
Article: main_krylov, thm:Fplanar, original one-correction policy. -/
def planeObservedCentreOutput (p r f₀ f₁ f₂ : ℝ) (g₀ g₁ g₂ : Plane) : Plane := by
  classical
  exact if g₂=0 then planeOfPair (p,r*p) else
    planeCentreOutput r p (planeObservedBinaryData p r f₀ f₁ f₂ g₀ g₁ g₂)

/-- Genuine stationary endpoint data require no final correction, for any
values or previous observations. Article: main_krylov, thm:Fplanar. -/
theorem planeObservedCentreOutput_stationary (p r f₀ f₁ f₂ : ℝ) (g₀ g₁ : Plane) :
    planeObservedCentreOutput p r f₀ f₁ f₂ g₀ g₁ 0=planeOfPair (p,r*p) := by
  classical
  rw [planeObservedCentreOutput,ite_eq_left rfl]

/-- The actual endpoint-only centre policy attains the sharp full tensor-ball
upper coefficient, uniformly with a fourth-order function remainder.
This is an implementable observed-data policy, including exact termination.
Article: main_krylov, thm:Fplanar. -/
theorem planeObservedCentreOutput_gradient_upper (r : ℝ) (hr : r≠0) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      let f := planeCubicObjective p r t
      let G := gradient f
      let x := planeObservedCentreOutput p r (f 0) (f (planeOfPair (p,0))) (f (planeOfPair (p,r*p)))
        (G 0) (G (planeOfPair (p,0))) (G (planeOfPair (p,r*p)))
      ‖G x‖≤r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r*p^3+C*p^4 := by
  classical
  obtain ⟨C,hC,hupper⟩ := planeCentreOutput_gradient_upper r
  refine ⟨C,hC,?_⟩
  intro p hp hp₁ t ht
  dsimp only
  unfold planeObservedCentreOutput
  split
  · rename_i hg
    rw [hg,norm_zero]
    have hm := (fibreMinimax_bounds r).1
    positivity
  · rw [planeObservedBinaryData_eq p r hp.ne' hr t]
    exact hupper p hp hp₁ t ht

end
end krylov.Functions
