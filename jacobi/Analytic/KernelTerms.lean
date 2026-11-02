import jacobi.Analytic.NormingProducts
import jacobi.Analytic.ReferenceEnergyContinuity
import jacobi.Analytic.ReferenceNormBounds
import jacobi.Analytic.OrderReferenceBounds
import jacobi.GelfandLevitan.KernelTerm

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The literal original GL summands have holomorphic complex-order
continuations on the actual common Bessel disk. Every norm denominator
is genuinely nonzero, and the real restriction is exactly the original
real kernel summand. Normal convergence of the infinite series remains
a separate estimate; it is not assumed in these pointwise statements.
Use: the analytic GL kernel is the normally convergent sum of these same continued source summands.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric jacobi.ComplexReference jacobi.Hankel
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The literal original GL summand at complex order on the genuine common numbered Bessel disk.
Use: the analytic GL kernel is the normally convergent sum of these same continued source summands.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def OrderDisk.kernelTerm {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) (t s : ℝ) (a : ℂ) : ℂ :=
  (D.normingRatio k a*solution a (D.spectrum k a) t*solution a (D.spectrum k a) s-
    solution a (frequencyReference a k) t*solution a (frequencyReference a k) s)/norming a k

/-- The actual norming product is continuous up to the boundary of the common closed order disk.
Use: preserves joint continuity of the GL summands on the compact domain used for their uniform majorant.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the finite products of the genuine continuous gap factors converge uniformly on this very closed disk. -/
theorem OrderDisk.normingRatio_continuousOn {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) :
    ContinuousOn (D.normingRatio k) (closedBall (a0:ℂ) D.radius) :=
  (D.normingRatio_uniform k).tendstoUniformlyOn.continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun s =>
      continuousOn_finsetProd s (fun l _ => D.normingFactor_continuousOn k l))))

/-- Every original continued GL summand is jointly continuous in order and both physical coordinates, even on the closed disk and singular endpoint edges.
Use: the normally convergent original series gives a jointly continuous analytic GL kernel, and compactness bounds its genuine finite prefix.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual spectral branches are continuous on a larger disk, the genuine norming products converge uniformly on the closed disk, and the original energy solutions are jointly continuous. Compose these maps and divide by the proved nonzero continuous reference norm. -/
theorem OrderDisk.kernelTerm_continuousOn {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) :
    ContinuousOn (fun p : ℂ × ℝ × ℝ => D.kernelTerm k p.2.1 p.2.2 p.1)
      (closedBall (a0:ℂ) D.radius ×ˢ (Icc (0:ℝ) (1/2) ×ˢ Icc (0:ℝ) (1/2))) := by
  -- All original parameters move together, including both singular spatial endpoints.
  intro p hp
  let U := closedBall (a0:ℂ) D.radius ×ˢ (Icc (0:ℝ) (1/2) ×ˢ Icc (0:ℝ) (1/2))
  have hfst : ContinuousWithinAt (fun q : ℂ × ℝ × ℝ => q.1) U p := continuousWithinAt_fst
  have ha : ‖p.1-(a0:ℂ)‖≤D.radius := by simpa only [mem_closedBall,dist_eq_norm] using hp.1
  have hag : 0<(gamma p.1).re := by have har := D.admissible ha; unfold gamma; norm_num; linarith
  have hS : ContinuousOn (D.spectrum k) (closedBall (a0:ℂ) D.radius) := (D.holomorphic k).continuousOn.mono
    (closedBall_subset_ball (by linarith [D.radius_pos]))
  have hSp := (hS p.1 hp.1).comp hfst (fun _ hq => hq.1)
  have hT : Continuous (fun a : ℂ => frequencyReference a k) := by
    unfold frequencyReference frequencyGrid besselCoefficient
    fun_prop
  have hTp := hT.continuousAt.comp_continuousWithinAt hfst
  have htp : ContinuousWithinAt (fun q : ℂ × ℝ × ℝ => q.2.1) U p :=
    continuousAt_fst.comp_continuousWithinAt (continuousAt_snd.continuousWithinAt)
  have hsp : ContinuousWithinAt (fun q : ℂ × ℝ × ℝ => q.2.2) U p :=
    continuousAt_snd.comp_continuousWithinAt (continuousAt_snd.continuousWithinAt)
  have hsolSt := (solution_joint_continuous (z := D.spectrum k p.1) hag
    (show p.2.1∈Ico 0 1 from ⟨hp.2.1.1,by linarith [hp.2.1.2]⟩)).comp_continuousWithinAt
      (f := fun q : ℂ × ℝ × ℝ => (q.1,D.spectrum k q.1,q.2.1))
      (hfst.prodMk (hSp.prodMk htp))
  have hsolSs := (solution_joint_continuous (z := D.spectrum k p.1) hag
    (show p.2.2∈Ico 0 1 from ⟨hp.2.2.1,by linarith [hp.2.2.2]⟩)).comp_continuousWithinAt
      (f := fun q : ℂ × ℝ × ℝ => (q.1,D.spectrum k q.1,q.2.2))
      (hfst.prodMk (hSp.prodMk hsp))
  have hsolTt := (solution_joint_continuous (z := frequencyReference p.1 k) hag
    (show p.2.1∈Ico 0 1 from ⟨hp.2.1.1,by linarith [hp.2.1.2]⟩)).comp_continuousWithinAt
      (f := fun q : ℂ × ℝ × ℝ => (q.1,frequencyReference q.1 k,q.2.1))
      (hfst.prodMk (hTp.prodMk htp))
  have hsolTs := (solution_joint_continuous (z := frequencyReference p.1 k) hag
    (show p.2.2∈Ico 0 1 from ⟨hp.2.2.1,by linarith [hp.2.2.2]⟩)).comp_continuousWithinAt
      (f := fun q : ℂ × ℝ × ℝ => (q.1,frequencyReference q.1 k,q.2.2))
      (hfst.prodMk (hTp.prodMk hsp))
  have hR := ((D.normingRatio_continuousOn k) p.1 hp.1).comp
    hfst (fun _ hq => hq.1)
  have hnorm := (norming_comp_analytic analyticAt_id hag k).continuousAt.comp_continuousWithinAt
    hfst
  exact (((hR.mul hsolSt).mul hsolSs).sub (hsolTt.mul hsolTs)).div hnorm (norming_ne_zero hag k)

/-- Every actual continued source GL summand is holomorphic in the complex order throughout the common spectral disk.
Use: supplies the original holomorphic terms of Appendix E.1,
with all continuation and norming-denominator conditions discharged.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the original numbered spectral branches and polynomial reference
energies are holomorphic. The true reference energy solution is analytic
along both curves, including their possible frequency branch points.
Multiply by the actual holomorphic norming product and divide by the
proved holomorphic nonzero original reference norm. -/
theorem OrderDisk.kernelTerm_holomorphic {a0 : ℝ} (D : OrderDisk a0) (k : ℕ)
    {t s : ℝ} (ht : t∈Icc 0 (1/2)) (hs : s∈Icc 0 (1/2)) :
    DifferentiableOn ℂ (D.kernelTerm k t s) (ball (a0:ℂ) D.radius) := by
  -- The original spectral branches, norm products and reference functions are kept together on one actual disk.
  intro a ha
  have har := D.admissible (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using ha))
  have hag : 0<(gamma a).re := by unfold gamma; norm_num; linarith
  have hS : AnalyticAt ℂ (D.spectrum k) a :=
    (D.holomorphic k).analyticOnNhd isOpen_ball a
      (ball_subset_ball (by linarith [D.radius_pos]) ha)
  have hT : AnalyticAt ℂ (fun b => frequencyReference b k) a := by
    unfold frequencyReference frequencyGrid besselCoefficient
    fun_prop
  have hsolS (u : ℝ) (hu : u∈Icc 0 (1/2)) :
      AnalyticAt ℂ (fun b => solution b (D.spectrum k b) u) a :=
    solution_comp_analytic analyticAt_id hS hag ⟨hu.1,by linarith [hu.2]⟩
  have hsolT (u : ℝ) (hu : u∈Icc 0 (1/2)) :
      AnalyticAt ℂ (fun b => solution b (frequencyReference b k) u) a :=
    solution_comp_analytic analyticAt_id hT hag ⟨hu.1,by linarith [hu.2]⟩
  have hR := (D.normingRatio_holomorphic k).analyticOnNhd isOpen_ball a ha
  exact ((((hR.mul (hsolS t ht)).mul (hsolS s hs)).sub
    ((hsolT t ht).mul (hsolT s hs))).div (norming_comp_analytic analyticAt_id hag k)
      (norming_ne_zero hag k)).differentiableAt.differentiableWithinAt

/-- The actual continued source GL summand is symmetric in its original physical coordinates.
Use: the genuine normally convergent kernel inherits symmetry term by term.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: commute the two reference-function factors in each of the literal numerator products. -/
theorem OrderDisk.kernelTerm_symmetric {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) (t s : ℝ) (a : ℂ) :
    D.kernelTerm k t s a=D.kernelTerm k s t a := by
  unfold OrderDisk.kernelTerm
  ring

/-- The continued GL summands agree exactly with the original real GL summands at every real order of the common disk.
Use: identifies the analytic kernel with the actual original source kernel once its uniform sum is established.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the continued numbered Bessel zeros, polynomial reference values,
actual gap products, reference energy functions and norm quotients all
have their proved original real values. Substitute them in the same
literal bilinear numerator and preserve the original real division. -/
theorem OrderDisk.kernelTerm_real {a0 b : ℝ} (D : OrderDisk a0) (hb : -1<b)
    (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤D.radius) (k : ℕ) {t s : ℝ}
    (ht : t∈Icc 0 (1/2)) (hs : s∈Icc 0 (1/2)) :
    D.kernelTerm k t s (b:ℂ)=(jacobi.GelfandLevitan.kernelTerm b hb k t s:ℂ) := by
  -- The comparison is termwise between the literal source formulas, including every finite spectral index.
  have hti : t∈Ico 0 1 := ⟨ht.1,by linarith [ht.2]⟩
  have hsi : s∈Ico 0 1 := ⟨hs.1,by linarith [hs.2]⟩
  rw [OrderDisk.kernelTerm,D.normingRatio_real hb hbd k,D.real_eq b hb hbd k,
    frequencyReference_ofReal,norming_real hb k,
    solution_real b _ hti,solution_real b _ hsi,solution_real b _ hti,solution_real b _ hsi]
  unfold jacobi.GelfandLevitan.kernelTerm
  push_cast
  rw [jacobi.Reference.realSolution_cast,jacobi.Reference.realSolution_cast,
    jacobi.Reference.realSolution_cast,jacobi.Reference.realSolution_cast]

end
end jacobi.Analytic
