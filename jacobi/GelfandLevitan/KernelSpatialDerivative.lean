import jacobi.GelfandLevitan.RegularizedDifferentiation
import jacobi.Reference.ZeroGreenFactorization

/-!
Article: jacobi, Theorem 2.1.
The Green derivative uses the large-coordinate branch, so its
diagonal derivative is correctly interpreted from within that branch.
Use: supplies dot F in the original equation for the t derivative of K; the true selected Green factor contributes its actual negative reflected slope.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] kernel regularizedKernel regularizedSlope realSolution

/-- The continuous large-first-coordinate derivative of the actual original GL kernel.
Use: supplies dot F in the original equation for the t derivative of K; the true selected Green factor contributes its actual negative reflected slope.
Article: jacobi, Theorem 2.1.
-/
def kernelSlope (a : ℝ) (ha : -1<a) (t s : ℝ) : ℝ :=
  -(displacementMass a ha*realSolution a (jacobi.Jacobi.endpointCorrection a) s*
    realSlope a (jacobi.Jacobi.endpointCorrection a) (1-t)/zeroGreenConstant a)+regularizedSlope a ha t s

/-- The actual original GL derivative data dot F extend continuously to every whole physical closed strip away from t=0.
Use: the original differentiated GL right-hand side has continuous triangular data, including s=0, the diagonal and the physical midpoint.
Article: jacobi, Theorem 2.1.
Proof: the original selected zero-energy solution is continuous at its own zero endpoint, its genuine reflected slope is continuous away from the opposite singular endpoint, and the actual regularized derivative series is jointly continuous on the closed strip. -/
theorem kernelSlope_continuousOn {a d : ℝ} (ha : -1<a) (hd : 0<d) :
    ContinuousOn (fun p : ℝ × ℝ => kernelSlope a ha p.1 p.2)
      (Icc d (1/2)×ˢIcc (0:ℝ) (1/2)) := by
  -- The explicit reflected slope stays in the nonsingular reference interior at every point of this strip.
  have hc : ContinuousOn (fun p : ℝ × ℝ =>
      -(displacementMass a ha*realSolution a (jacobi.Jacobi.endpointCorrection a) p.2*
        realSlope a (jacobi.Jacobi.endpointCorrection a) (1-p.1)/zeroGreenConstant a))
      (Icc d (1/2)×ˢIcc (0:ℝ) (1/2)) := by
    intro p hp
    have hr : 1-p.1∈Ioo (0:ℝ) 1 := ⟨by linarith [hp.1.2],by linarith [hd.trans_le hp.1.1]⟩
    have hsol := (realSolution_continuousAt ha (jacobi.Jacobi.endpointCorrection a) hp.2).comp_of_eq continuousAt_snd rfl
    have hslope := (realSlope_continuousAt a (jacobi.Jacobi.endpointCorrection a) hr).comp_of_eq
      (continuousAt_const.sub continuousAt_fst : ContinuousAt (fun q : ℝ × ℝ => 1-q.1) p) rfl
    exact ((((continuousAt_const.mul hsol).mul hslope).div_const _).neg).continuousWithinAt
  exact hc.add (regularizedSlope_continuousOn ha hd)

/-- The original Green factor has its genuine large-coordinate spatial derivative, including the one-sided diagonal interpretation.
Use: kernel_hasDerivWithinAt combines this actual Green derivative with the complete original regularized derivative theorem to obtain the true dot F.
Article: jacobi, Theorem 2.1.
Proof: on the required interval the original min/max factor equals chi(s)*chi(1-t)/W_0. Differentiate the genuine reflected selected solution and restrict its derivative to that same physical interval. -/
theorem zeroGreenKernel_hasDerivWithinAt {a d t s : ℝ} (ha : -1<a) (hd : 0<d)
    (ht : t∈Icc (max d s) (1/2)) (hs : 0≤s) :
    HasDerivWithinAt (fun x => zeroGreenKernel a x s)
      (-(realSolution a (jacobi.Jacobi.endpointCorrection a) s*
        realSlope a (jacobi.Jacobi.endpointCorrection a) (1-t)/zeroGreenConstant a))
      (Icc (max d s) (1/2)) t := by
  -- The min/max branch is fixed on the interval, including the actual source diagonal.
  have hdt : d≤t := (le_max_left d s).trans ht.1
  have hst : s≤t := (le_max_right d s).trans ht.1
  have hrt : 1-t∈Ioo (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [hd.trans_le hdt]⟩
  have hchi : HasDerivAt (fun x : ℝ => realSolution a (jacobi.Jacobi.endpointCorrection a) (1-x))
      (-realSlope a (jacobi.Jacobi.endpointCorrection a) (1-t)) t := by
    convert (realSolution_hasDerivAt a (jacobi.Jacobi.endpointCorrection a) hrt).comp t
      ((hasDerivAt_id t).const_sub 1) using 1
    · rfl
    · ring
  have hder := ((hchi.const_mul (realSolution a (jacobi.Jacobi.endpointCorrection a) s)).div_const (zeroGreenConstant a)).hasDerivWithinAt
    (s := Icc (max d s) (1/2))
  have he (x : ℝ) (hx : x∈Icc (max d s) (1/2)) :
      zeroGreenKernel a x s=realSolution a (jacobi.Jacobi.endpointCorrection a) s*
        realSolution a (jacobi.Jacobi.endpointCorrection a) (1-x)/zeroGreenConstant a := by
    have hsx : s≤x := (le_max_right d s).trans hx.1
    rw [zeroGreen_factorization ha ⟨(hd.trans_le ((le_max_left d s).trans hx.1)).le,hx.2⟩ ⟨hs,hst.trans ht.2⟩,
      zeroGreenFactor,min_eq_right hsx,max_eq_left hsx]
  convert hder.congr he (he t ht) using 1
  ring

/-- The actual original F has dot F as its genuine first-coordinate derivative on each closed physical lower-triangle slice.
Use: the t-differentiated original GL equation uses exactly these proved continuous data; derivatives at the diagonal and midpoint are taken within the printed physical interval.
Article: jacobi, Theorem 2.1.
Proof: add the actual Green branch derivative to the independently proved original regularized derivative. Their sum agrees exactly with the previously constructed original F on the same physical interval. -/
theorem kernel_hasDerivWithinAt {a d t s : ℝ} (ha : -1<a) (hd : 0<d)
    (ht : t∈Icc (max d s) (1/2)) (hs : 0≤s) :
    HasDerivWithinAt (fun x => kernel a ha x s) (kernelSlope a ha t s)
      (Icc (max d s) (1/2)) t := by
  -- Differentiate the already identified original decomposition, keeping the two actual summands separate.
  have hst : s≤t := (le_max_right d s).trans ht.1
  have hreg := regularizedKernel_hasDerivWithinAt ha (lt_of_lt_of_le hd (le_max_left d s)) ht ⟨hs,hst.trans ht.2⟩
  have hgreen := (zeroGreenKernel_hasDerivWithinAt ha hd ht hs).const_mul (displacementMass a ha)
  have he : (fun x => regularizedKernel a ha x s+displacementMass a ha*zeroGreenKernel a x s)=
      (fun x => kernel a ha x s) := by funext x; rw [regularizedKernel]; ring
  have hder := hreg.add hgreen
  change HasDerivWithinAt (fun x => regularizedKernel a ha x s+displacementMass a ha*zeroGreenKernel a x s) _ _ _ at hder
  rw [he] at hder
  convert hder using 1
  unfold kernelSlope
  ring

end
end jacobi.GelfandLevitan
