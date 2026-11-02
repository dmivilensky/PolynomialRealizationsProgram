import jacobi.Analytic.KernelUniform
import jacobi.Analytic.ContinuousMapHolomorphy

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The actual normally convergent kernel is holomorphic with values in the
Banach space of continuous functions on the physical half square.
This is norm holomorphy, not merely a collection of scalar assertions.
Use: fixes the Banach space of actual continuous GL kernels in analytic operator inversion.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local irreducible] OrderDisk.kernel OrderDisk.kernelTerm

/-- The compact physical half square, with both endpoint edges retained.
Use: fixes the Banach space of actual continuous GL kernels in analytic operator inversion.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
abbrev KernelSquare := (Icc (0:ℝ) (1/2)) × (Icc (0:ℝ) (1/2))

/-- The genuine kernel at each admissible disk order is continuous in its physical variables.
Use: packages the actual uniformly convergent GL series as a continuous function, rather than choosing a different representative.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: restrict the proved joint continuity on the closed product domain to the fixed order and the subtype coordinates of the physical half square. -/
theorem OrderDisk.kernel_spatial_continuous {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (ha : ‖a-(a0:ℂ)‖≤D.radius) :
    Continuous (fun p : KernelSquare => D.kernel a p.1 p.2) :=
  D.kernel_continuousOn.comp_continuous
    (f := fun p : KernelSquare => (a,(p.1:ℝ),(p.2:ℝ)))
    (show Continuous (fun p : KernelSquare => (a,(p.1:ℝ),(p.2:ℝ))) by fun_prop)
    (fun p => ⟨by simpa only [mem_closedBall,dist_eq_norm] using ha,p.1.property,p.2.property⟩)

/-- The actual complex GL kernel in the Banach space of continuous physical kernels.
Use: supplies the norm-holomorphic kernel parameter for the genuine continued integral operator.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The arbitrary zero value outside the estimation disk only makes this a total Lean function; every mathematical assertion below concerns the original disk. -/
def OrderDisk.kernelMap {a0 : ℝ} (D : OrderDisk a0) (a : ℂ) : C(KernelSquare,ℂ) :=
  if ha : ‖a-(a0:ℂ)‖≤D.radius then ⟨fun p => D.kernel a p.1 p.2,D.kernel_spatial_continuous ha⟩ else 0

/-- The continuous-kernel-valued map evaluates to the literal original complex GL sum at every disk order and physical pair.
Use: identifies the Banach-valued analytic construction with all scalar kernel and real restriction statements.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: on the proved estimation disk the definition uses the genuine continuous kernel, so evaluation reduces directly. -/
theorem OrderDisk.kernelMap_apply {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (ha : ‖a-(a0:ℂ)‖≤D.radius) (p : KernelSquare) :
    D.kernelMap a p=D.kernel a p.1 p.2 := by
  simp only [OrderDisk.kernelMap,dite_eq_left ha,ContinuousMap.coe_mk]

/-- The genuine kernel is continuous in the continuous-function norm throughout the closed common order disk.
Use: supplies the norm continuity needed to perturb the actual GL operator at the real base order.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: joint continuity of the actual kernel on the disk times the compact physical square gives continuity of its curried map in the compact-open topology, which is the continuous-function norm topology here. -/
theorem OrderDisk.kernelMap_continuousOn {a0 : ℝ} (D : OrderDisk a0) :
    ContinuousOn D.kernelMap (closedBall (a0:ℂ) D.radius) := by
  -- Compact spatial currying turns genuine joint continuity into uniform norm continuity.
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  have hc : ContinuousOn (fun q : ℂ × KernelSquare => D.kernel q.1 q.2.1 q.2.2)
      (closedBall (a0:ℂ) D.radius ×ˢ univ) :=
    D.kernel_continuousOn.comp (f := fun q : ℂ × KernelSquare => (q.1,(q.2.1:ℝ),(q.2.2:ℝ))) (show ContinuousOn
      (fun q : ℂ × KernelSquare => (q.1,(q.2.1:ℝ),(q.2.2:ℝ))) _ by fun_prop)
      (fun q hq => ⟨hq.1,q.2.1.property,q.2.2.property⟩)
  exact hc.congr (fun q hq => D.kernelMap_apply
    (by simpa only [mem_closedBall,dist_eq_norm] using hq.1) q.2)

/-- The actual continued GL kernel is holomorphic in the Banach norm of continuous physical kernels on the common open order disk.
Use: the genuine integral operators and their local inverses depend analytically on order in operator norm.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual kernel map is norm-continuous and every point evaluation is the proved original scalar holomorphic kernel. The continuous-function-valued Cauchy integral theorem therefore gives a Banach derivative. -/
theorem OrderDisk.kernelMap_holomorphic {a0 : ℝ} (D : OrderDisk a0) :
    DifferentiableOn ℂ D.kernelMap (ball (a0:ℂ) D.radius) := by
  apply continuousMap_differentiableOn isOpen_ball (D.kernelMap_continuousOn.mono ball_subset_closedBall)
  intro p
  exact (D.kernel_holomorphic p.1.property p.2.property).congr (fun a ha =>
    D.kernelMap_apply (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using ha)) p)

/-- The original complex GL kernel satisfies the complete normal-convergence, continuity and Banach-holomorphy assertion on an actual common numbered Bessel disk at every admissible real base order.
Use: supplies Appendix E.1 with no unproved spectral, asymptotic or reference-function premise for the following analytic GL inversion.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: obtain the genuine disk from the proved original Bessel theorem, then combine the full-index summand majorant, joint continuity, uniform convergence, symmetry, continuous-function-valued holomorphy and exact real-series identification. -/
theorem analytic_kernel {a0 : ℝ} (ha0 : -1<a0) :
    ∃ D : OrderDisk a0,∃ C : ℝ,0<C ∧
      (∀ a : ℂ,‖a-(a0:ℂ)‖≤D.radius → ∀ k : ℕ,
        ∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),‖D.kernelTerm k t s a‖≤C/(k+1:ℝ)^2) ∧
      ContinuousOn (fun p : ℂ × ℝ × ℝ => D.kernel p.1 p.2.1 p.2.2)
        (closedBall (a0:ℂ) D.radius ×ˢ (Icc (0:ℝ) (1/2) ×ˢ Icc (0:ℝ) (1/2))) ∧
      TendstoUniformlyOn
        (fun N : ℕ => fun p : ℂ × ℝ × ℝ => ∑ k∈Finset.range N,D.kernelTerm k p.2.1 p.2.2 p.1)
        (fun p : ℂ × ℝ × ℝ => D.kernel p.1 p.2.1 p.2.2) atTop
        (closedBall (a0:ℂ) D.radius ×ˢ (Icc (0:ℝ) (1/2) ×ˢ Icc (0:ℝ) (1/2))) ∧
      DifferentiableOn ℂ D.kernelMap (ball (a0:ℂ) D.radius) ∧
      (∀ a t s,D.kernel a t s=D.kernel a s t) ∧
      (∀ b : ℝ,∀ hb : -1<b,‖(b:ℂ)-(a0:ℂ)‖≤D.radius →
        ∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),
          D.kernel (b:ℂ) t s=(jacobi.GelfandLevitan.kernel b hb t s:ℂ)) := by
  obtain ⟨D⟩ := orderDisk_nonempty ha0
  obtain ⟨C,hC,hbound⟩ := D.kernelTerm_uniform_bound
  exact ⟨D,C,hC,hbound,D.kernel_continuousOn,D.kernel_uniform_limit,
    D.kernelMap_holomorphic,D.kernel_symmetric,fun b hb hbd _ ht _ hs => D.kernel_real hb hbd ht hs⟩

end
end jacobi.Analytic
