import polyak.Boundary.P2.Weights
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Differentiated two-atom primal–dual pairing: double contacts remove all
atom and mass derivatives from the value equation. -/
noncomputable section
namespace polyak.Boundary.Envelope
open Filter
open scoped Topology

abbrev Point := Fin 3 → ℝ

def point (u G c : ℝ) : Point := ![u,G,c]
def basis (i : Fin 3) : Point := Pi.single i 1

theorem linear_apply (L : Point →L[ℝ] ℝ) (v : Point) :
    L v=v 0*L (basis 0)+v 1*L (basis 1)+v 2*L (basis 2) := by
  have he : v=v 0 • basis 0+v 1 • basis 1+v 2 • basis 2 := by
    ext i
    fin_cases i <;> simp [basis]
  calc
    L v=L (v 0 • basis 0+v 1 • basis 1+v 2 • basis 2) := congrArg L he
    _=_ := by simp only [map_add,map_smul,smul_eq_mul]

theorem point_hasDerivAt {u G c : ℝ → ℝ} {du dG dc s : ℝ}
    (hu : HasDerivAt u du s) (hG : HasDerivAt G dG s) (hc : HasDerivAt c dc s) :
    HasDerivAt (fun r => point (u r) (G r) (c r)) (point du dG dc) s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hu
  · exact hG
  · exact hc

/-- A zero contact and a zero frequency derivative remove the frequency velocity. -/
theorem contact_hasDerivAt {D : Point → ℝ} {u G c : ℝ → ℝ}
    {du dG dc s : ℝ} (hD : DifferentiableAt ℝ D (point (u s) (G s) (c s)))
    (hu : HasDerivAt u du s) (hG : HasDerivAt G dG s) (hc : HasDerivAt c dc s)
    (hc0 : fderiv ℝ D (point (u s) (G s) (c s)) (basis 2)=0) :
    HasDerivAt (fun r => D (point (u r) (G r) (c r)))
      (du*fderiv ℝ D (point (u s) (G s) (c s)) (basis 0)+
       dG*fderiv ℝ D (point (u s) (G s) (c s)) (basis 1)) s := by
  have hd:=hD.hasFDerivAt.comp_hasDerivAt s (point_hasDerivAt hu hG hc)
  rw [linear_apply] at hd
  change HasDerivAt (fun r => D (point (u r) (G r) (c r)))
    (du*fderiv ℝ D (point (u s) (G s) (c s)) (basis 0)+
     dG*fderiv ℝ D (point (u s) (G s) (c s)) (basis 1)+
     dc*fderiv ℝ D (point (u s) (G s) (c s)) (basis 2)) s at hd
  simpa only [hc0,mul_zero,add_zero] using hd

/-- Differentiating a two-atom pairing at double contacts leaves only u′ and G′. -/
theorem twoAtom_derivative {D : Point → ℝ} {u G p x y : ℝ → ℝ}
    {du dG dp dx dy s : ℝ}
    (hu : HasDerivAt u du s) (hG : HasDerivAt G dG s) (hp : HasDerivAt p dp s)
    (hx : HasDerivAt x dx s) (hy : HasDerivAt y dy s)
    (hDx : DifferentiableAt ℝ D (point (u s) (G s) (x s)))
    (hDy : DifferentiableAt ℝ D (point (u s) (G s) (y s)))
    (hx0 : D (point (u s) (G s) (x s))=0)
    (hy0 : D (point (u s) (G s) (y s))=0)
    (hxc : fderiv ℝ D (point (u s) (G s) (x s)) (basis 2)=0)
    (hyc : fderiv ℝ D (point (u s) (G s) (y s)) (basis 2)=0)
    (hzero : (fun r => (1-p r)*D (point (u r) (G r) (x r))+
      p r*D (point (u r) (G r) (y r))) =ᶠ[𝓝 s] (fun _ => 0)) :
    ((1-p s)*fderiv ℝ D (point (u s) (G s) (x s)) (basis 0)+
      p s*fderiv ℝ D (point (u s) (G s) (y s)) (basis 0))*du+
    ((1-p s)*fderiv ℝ D (point (u s) (G s) (x s)) (basis 1)+
      p s*fderiv ℝ D (point (u s) (G s) (y s)) (basis 1))*dG=0 := by
  have hdx:=contact_hasDerivAt hDx hu hG hx hxc
  have hdy:=contact_hasDerivAt hDy hu hG hy hyc
  have hd:=(((hasDerivAt_const s (1 : ℝ)).sub hp).mul hdx).add (hp.mul hdy)
  have hval:=hd.unique ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hzero)
  rw [hx0,hy0] at hval
  dsimp only [Pi.sub_apply] at hval
  linear_combination hval

end polyak.Boundary.Envelope
