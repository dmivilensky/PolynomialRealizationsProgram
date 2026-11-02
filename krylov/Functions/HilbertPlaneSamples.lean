import krylov.Functions.HilbertPlaneObjective
import krylov.Functions.PlanarFiniteRadius

/-!
Article: main_krylov, prop:Fcycle(iii), genuine first/middle/last gradients.
Use: identify the actual full cubic gradients on the real three-sample
reference geometry, before applying global CG consistency. Source: exact
coordinate polynomial differentiation of the original scalar cubic family.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The two original real coordinate conversions are genuine inverses.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planeOfPair_pairOfPlane (z : Plane) : planeOfPair (pairOfPlane z)=z := by
  ext i
  fin_cases i <;> rfl

/-- The common actual terminal point of the reference quadratic, retaining
its orthogonal-complement displacement. Article: prop:Fcycle(iii). -/
def hilbertPlaneTerminal (e h m : E) (p r : ℝ) : E :=
  hilbertPlaneEmbed e h (planeOfPair (p,r*p))+m

/-- The full true gradient is the original common reference gradient plus
the true two-coordinate cubic perturbation. Article: prop:Fcycle(iii). -/
theorem hilbertPlaneGradient_reference_formula (e h m : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x : E) :
    gradient (hilbertPlaneObjective e h m p r t) x=
      x-hilbertPlaneTerminal e h m p r+
        hilbertPlaneEmbed e h (planeOfPair
          (planarValueCoordinateDerivative p r t (pairOfPlane (hilbertPlaneProject e h x)))) := by
  rw [hilbertPlaneGradient_actual,hilbertPlaneGradient,planeCubicGradient_actual,
    planeCubicGradient,planarCubicGradient,planeOfPair_add,planeOfPair_sub,
    planeOfPair_pairOfPlane,map_add,map_sub]
  dsimp only [hilbertPlaneTerminal]
  abel

/-- At every actual first or middle planar sample, the true full gradient
is exactly the common quadratic gradient. Article: prop:Fcycle(iii). -/
theorem hilbertPlaneGradient_prefix_sample (e h m : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x : E)
    (hx : (inner ℝ e x=0 ∧ inner ℝ h x=0) ∨ (inner ℝ e x=p ∧ inner ℝ h x=0)) :
    gradient (hilbertPlaneObjective e h m p r t) x=x-hilbertPlaneTerminal e h m p r := by
  have hz : planarValueCoordinateDerivative p r t (pairOfPlane (hilbertPlaneProject e h x))=0 := by
    rcases hx with hx | hx
    · ext <;> simp [planarValueCoordinateDerivative,hilbertPlaneProject_apply,pairOfPlane,planeOfPair,hx.1,hx.2]
    · ext <;> simp [planarValueCoordinateDerivative,hilbertPlaneProject_apply,pairOfPlane,planeOfPair,hx.1,hx.2] <;> ring
  rw [hilbertPlaneGradient_reference_formula,hz]
  have hp : planeOfPair (0 : ℝ × ℝ)=0 := by ext i; fin_cases i <;> rfl
  rw [hp,map_zero,add_zero]

/-- The common true terminal gradient is precisely the genuine observed
binary scalar P, in the first reference direction. Article: prop:Fcycle(iii). -/
theorem hilbertPlaneGradient_terminal (e h m : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (hm : hilbertPlaneProject e h m=0)
    (p r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    gradient (hilbertPlaneObjective e h m p r t) (hilbertPlaneTerminal e h m p r)=
      (p^2*r/2*(t.t1+r*t.t2)) • e := by
  have hcoords : hilbertPlaneProject e h (hilbertPlaneTerminal e h m p r)=planeOfPair (p,r*p) := by
    rw [hilbertPlaneTerminal,map_add,hilbertPlaneProject_embed e h he hh heh,hm,add_zero]
  rw [hilbertPlaneGradient_reference_formula,sub_self,zero_add,hcoords,pairOfPlane_planeOfPair]
  have hg : planarValueCoordinateDerivative p r t (p,r*p)=(p^2*r/2*(t.t1+r*t.t2),0) := by
    ext <;> simp only [planarValueCoordinateDerivative] <;> ring
  rw [hg,hilbertPlaneEmbed_apply]
  simp only [planeOfPair,Matrix.cons_val_zero,Matrix.cons_val_one,zero_smul,add_zero]

end
end krylov.Functions
