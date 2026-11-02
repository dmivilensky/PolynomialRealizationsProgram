import krylov.Convergence.ObservableEnergy
import krylov.Functions.ObservableRFCMetric

/-!
Article: main_krylov, apG:Dunif, genuine raw RFC model-energy bounds.
Use: transfer the normalized conditioning bounds to the actual raw
coefficient solve and its true physical correction, preserving the exact
observed energy. Source: true diagonal solve/energy invariance, finite
quadratic forms and the actual model normal equation.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions krylov.XR
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The actually solved raw rectangular model has the same sharp uniform
energy/length comparison and exact negative slope as its derived
well-conditioned normalized solve. Article: main_krylov, apG:Dunif. -/
theorem observable_raw_model_energy (s y : Fin p → E) (hs : ∀ i,s i≠0) (g : E)
    (hG : ‖crossGram (unitWindow s) (unitWindow s)-1‖≤1/4)
    (hM : ‖rescaleModel (pairModel s y) (fun i=>‖s i‖⁻¹)-1‖≤1/4)
    (hunit : IsUnit (pairModel s y).det) :
    let w := modelCoefficients s (pairModel s y) g
    let u := combine s w
    let energy := w ⬝ᵥ (pairModel s y*ᵥw)
    0≤energy ∧ ‖u‖^2≤(5/3:ℝ)*energy ∧ energy≤(5/3:ℝ)*‖u‖^2 ∧
      inner ℝ g u= -energy := by
  let M := pairModel s y
  let D := fun i=>‖s i‖⁻¹
  let Hn := rescaleModel M D
  let wn := modelCoefficients (unitWindow s) Hn g
  have hD := unitWindow_diagonal_unit s hs
  have hcorrection : combine (unitWindow s) wn=combine s (modelCoefficients s M g) :=
    modelCorrection_rescale s M D hD g
  have henergy : wn ⬝ᵥ (Hn*ᵥwn)=modelCoefficients s M g ⬝ᵥ (M*ᵥmodelCoefficients s M g) :=
    modelEnergy_rescale s M D hD g
  have hh := observable_energy_synthesis (unitWindow s) Hn hG hM wn
  rw [hcorrection,henergy] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2,modelVirtualCorrection_slope s M hunit g⟩

end
end krylov.Convergence
