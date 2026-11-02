import jacobi.Analytic.GLTriangle
import jacobi.Analytic.GLReal

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
At every original admissible base order one common complex disk carries
the genuine unique continuous triangular GL kernel, uniformly bounded
and pointwise holomorphic, with exact original real identification.
The physical L2 inverse estimate and the common-disk combined assertion
are proved in L2Inverse and HolomorphicGL.
Use: proves the spatially pointwise K holomorphy required for the original transformed solutions and analytic energy.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric jacobi.Reference jacobi.GelfandLevitan
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every actual triangular GL kernel value is holomorphic on an order subdisk where the genuine square operator remains invertible.
Use: proves the spatially pointwise K holomorphy required for the original transformed solutions and analytic energy.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the true square solution is holomorphic in its continuous-kernel norm. Compose with the bounded complex-linear evaluation at the same original triangle point. -/
theorem OrderDisk.GLtriangle_holomorphic {a0 r : ℝ} (D : OrderDisk a0)
    (hrD : r≤D.radius) (hunit : ∀ a∈ball (a0:ℂ) r,IsUnit (D.GLoperator a)) (p : Triangle) :
    DifferentiableOn ℂ (fun a => D.GLtriangle a p) (ball (a0:ℂ) r) := by
  intro a ha
  have he := (ContinuousMap.evalCLM ℂ p.val).differentiableAt (x := D.GLsolution a)
  convert! he.comp_differentiableWithinAt (F := C(KernelSquare,ℂ)) (G := ℂ) a
    (D.GLsolution_holomorphic hrD hunit a ha) using 1

/-- Every actual analytic triangular kernel value at real disk order is the unchanged original real transformation kernel value.
Use: verifies the original real restriction of the continued GL solution and all physical transformation integrals.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: evaluate the proved full-square real kernel equality at the original triangular coordinate pair. -/
theorem OrderDisk.GLtriangle_real {a0 b : ℝ} (D : OrderDisk a0) (hb : -1<b)
    (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤D.radius) (p : Triangle) :
    D.GLtriangle (b:ℂ) p=(transformationKernel b hb p.val.1 p.val.2:ℂ) :=
  congrArg (fun f : C(KernelSquare,ℂ) => f p.val) (D.GLsolution_real hb hbd)

/-- On one genuine complex neighborhood of every real base order, the original square GL solution is uniformly bounded and holomorphic and its operator is a true unit.
Use: supplies all continuous-kernel inverse and uniform-bound premises for the analytic transformed profile construction from the actual article data alone.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: use the proved common bounded-inverse disk. The original kernel is norm-continuous on the larger compact closed order disk and therefore uniformly bounded. Multiply the two true norm bounds to bound the actual inverse image of the original forcing, and use the already proved holomorphic inversion theorem on the open smaller disk. -/
theorem OrderDisk.GLsolution_local {a0 : ℝ} (D : OrderDisk a0) (ha0 : -1<a0) :
    ∃ r C : ℝ,0<r ∧ r<D.radius ∧ 0<C ∧
      (∀ a : ℂ,‖a-(a0:ℂ)‖≤r → IsUnit (D.GLoperator a) ∧ ‖D.GLsolution a‖≤C) ∧
      DifferentiableOn ℂ D.GLsolution (ball (a0:ℂ) r) := by
  -- The constants come from the actual original kernel and inverse on their genuine common compact disk.
  obtain ⟨r,M,hr,hrD,hM,hinv⟩ := D.GLoperator_local_inverse ha0
  obtain ⟨B,hB⟩ := (isCompact_closedBall (a0:ℂ) D.radius).exists_bound_of_continuousOn D.kernelMap_continuousOn
  let C : ℝ := M*(|B|+1)+1
  have hC : 0<C := by dsimp [C]; positivity
  have hunit : ∀ a∈ball (a0:ℂ) r,IsUnit (D.GLoperator a) :=
    fun a ha => (hinv a (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using ha))).1
  refine ⟨r,C,hr,hrD,hC,?_,D.GLsolution_holomorphic hrD.le hunit⟩
  intro a ha
  refine ⟨(hinv a ha).1,?_⟩
  have hFa : ‖D.kernelMap a‖≤|B|+1 :=
    (hB a (by simpa only [mem_closedBall,dist_eq_norm] using ha.trans hrD.le)).trans (by linarith [le_abs_self B])
  rw [OrderDisk.GLsolution,norm_neg]
  have hh := (Ring.inverse (D.GLoperator a)).le_opNorm (D.kernelMap a)
  have hm := mul_le_mul (hinv a ha).2 hFa (norm_nonneg _) hM.le
  exact hh.trans (hm.trans (by dsimp [C]; linarith))

/-- The original article data admit a unique uniformly bounded holomorphic continuous triangular GL kernel on one common complex order disk, with exact real restriction.
Use: closes the continuous-solution assertions of Appendix E.1 without unproved spectral, inverse or regularity hypotheses, before the separate L2 norm statement.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: obtain the actual original numbered Bessel disk and its proved bounded analytic inverse subdisk. Restrict the true square solution to the physical triangle. Its literal GL equation and arbitrary triangular uniqueness are proved independently, evaluation preserves the uniform bound and holomorphy, and the exact original real equality is already established. -/
theorem analytic_GL_continuous {a0 : ℝ} (ha0 : -1<a0) :
    ∃ D : OrderDisk a0,∃ r C : ℝ,0<r ∧ r<D.radius ∧ 0<C ∧
      (∀ a : ℂ,‖a-(a0:ℂ)‖≤r →
        (∃! K : C(Triangle,ℂ),D.SatisfiesGL a K) ∧
          ∀ p : Triangle,‖D.GLtriangle a p‖≤C) ∧
      (∀ p : Triangle,DifferentiableOn ℂ (fun a => D.GLtriangle a p) (ball (a0:ℂ) r)) ∧
      (∀ b : ℝ,∀ hb : -1<b,‖(b:ℂ)-(a0:ℂ)‖≤r → ∀ p : Triangle,
        D.GLtriangle (b:ℂ) p=(transformationKernel b hb p.val.1 p.val.2:ℂ)) := by
  -- Every hypothesis for the continued construction is supplied from the admissible real article parameter.
  obtain ⟨D⟩ := orderDisk_nonempty ha0
  obtain ⟨r,C,hr,hrD,hC,hdata,_⟩ := D.GLsolution_local ha0
  have hunit : ∀ a∈ball (a0:ℂ) r,IsUnit (D.GLoperator a) :=
    fun a ha => (hdata a (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using ha))).1
  refine ⟨D,r,C,hr,hrD,hC,?_,D.GLtriangle_holomorphic hrD.le hunit,?_⟩
  · intro a ha
    obtain ⟨hu,hbound⟩ := hdata a ha
    exact ⟨⟨D.GLtriangle a,D.GLtriangle_satisfiesGL hu,D.GLtriangle_unique hu⟩,
      fun p => ((D.GLsolution a).norm_coe_le_norm p.val).trans hbound⟩
  · intro b hb hbd p
    exact D.GLtriangle_real hb (hbd.trans hrD.le) p

end
end jacobi.Analytic
