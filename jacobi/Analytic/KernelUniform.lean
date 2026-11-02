import jacobi.Analytic.KernelMajorant
import jacobi.GelfandLevitan.UniformKernel

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The literal complex-order GL series converges absolutely and uniformly
on the common closed order disk times the entire physical half square.
Its sum is jointly continuous, symmetric, holomorphic in order and equal
to the original real GL kernel on the real axis.
Use: supplies the kernel of the continued GL integral equation and transformed profile.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric Filter jacobi.ComplexReference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The analytic continuation of the original GL kernel, as the sum of its actual continued summands.
Use: supplies the kernel of the continued GL integral equation and transformed profile.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def OrderDisk.kernel {a0 : ℝ} (D : OrderDisk a0) (a : ℂ) (t s : ℝ) : ℂ :=
  ∑' k,D.kernelTerm k t s a

/-- The genuine continued kernel series is absolutely summable at every point of its closed order and physical domain.
Use: justifies its sum, real identification and subsequent bounded operator construction.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: compare the actual summand norms with the proved common coefficient times the shifted inverse-square p-series. -/
theorem OrderDisk.kernel_absolute_summable {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (ha : ‖a-(a0:ℂ)‖≤D.radius) {t s : ℝ} (ht : t∈Icc 0 (1/2)) (hs : s∈Icc 0 (1/2)) :
    Summable (fun k => ‖D.kernelTerm k t s a‖) := by
  obtain ⟨C,_,hbound⟩ := D.kernelTerm_uniform_bound
  have hM : Summable (fun k : ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  exact hM.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hbound a ha k t ht s hs)

/-- The actual continued GL series converges uniformly simultaneously in complex order and both original physical coordinates.
Use: establishes the common-disk uniform convergence required for the analytic GL operator and its real restriction.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the proved full-index inverse-square bound supplies one genuinely summable majorant on the whole product domain. Apply the community uniform-series theorem to the literal source summands. -/
theorem OrderDisk.kernel_uniform_limit {a0 : ℝ} (D : OrderDisk a0) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : ℂ × ℝ × ℝ => ∑ k∈Finset.range N,D.kernelTerm k p.2.1 p.2.2 p.1)
      (fun p : ℂ × ℝ × ℝ => D.kernel p.1 p.2.1 p.2.2) atTop
      (closedBall (a0:ℂ) D.radius ×ˢ (Icc (0:ℝ) (1/2) ×ˢ Icc (0:ℝ) (1/2))) := by
  obtain ⟨C,_,hbound⟩ := D.kernelTerm_uniform_bound
  have hM : Summable (fun k : ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  exact tendstoUniformlyOn_tsum_nat hM (fun k p hp =>
    hbound p.1 (by simpa only [mem_closedBall,dist_eq_norm] using hp.1) k p.2.1 hp.2.1 p.2.2 hp.2.2)

/-- The actual continued GL kernel is jointly continuous on its entire closed order and physical domain.
Use: its continuous representative defines the analytic GL integral operators, including the endpoint rows.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the literal finite sums are jointly continuous by the proved continuity of the original summands; their uniform limit on this same product domain is continuous. -/
theorem OrderDisk.kernel_continuousOn {a0 : ℝ} (D : OrderDisk a0) :
    ContinuousOn (fun p : ℂ × ℝ × ℝ => D.kernel p.1 p.2.1 p.2.2)
      (closedBall (a0:ℂ) D.radius ×ˢ (Icc (0:ℝ) (1/2) ×ˢ Icc (0:ℝ) (1/2))) :=
  D.kernel_uniform_limit.continuousOn (Filter.Frequently.of_forall (fun N =>
    continuousOn_finsetSum (Finset.range N) (fun k _ => D.kernelTerm_continuousOn k)))

/-- The actual infinite GL kernel is holomorphic in the complex order at every fixed physical pair.
Use: provides the pointwise holomorphy entering its continuous-function-valued holomorphic realization.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: each genuine summand is holomorphic on the open disk and bounded there by the same proved summable inverse-square majorant. The community normal-series theorem gives holomorphy of their actual sum. -/
theorem OrderDisk.kernel_holomorphic {a0 : ℝ} (D : OrderDisk a0) {t s : ℝ}
    (ht : t∈Icc 0 (1/2)) (hs : s∈Icc 0 (1/2)) :
    DifferentiableOn ℂ (fun a => D.kernel a t s) (ball (a0:ℂ) D.radius) := by
  obtain ⟨C,_,hbound⟩ := D.kernelTerm_uniform_bound
  have hM : Summable (fun k : ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  exact _root_.Complex.differentiableOn_tsum_of_summable_norm hM
    (fun k => D.kernelTerm_holomorphic k ht hs) isOpen_ball
    (fun k a ha => hbound a (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using ha)) k t ht s hs)

/-- The actual continued infinite GL kernel retains its original bilinear symmetry.
Use: the analytic integral operators preserve the source symmetric kernel, without inserting complex conjugates.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the two literal infinite sums have equal summands by the proved actual summand symmetry. -/
theorem OrderDisk.kernel_symmetric {a0 : ℝ} (D : OrderDisk a0) (a : ℂ) (t s : ℝ) :
    D.kernel a t s=D.kernel a s t := tsum_congr (fun k => D.kernelTerm_symmetric k t s a)

/-- The actual analytic GL kernel agrees with the entire original real GL series at every real order in the common closed disk.
Use: the continued operator and GL solution specialize to the already constructed real source objects.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: real inclusion commutes with the original sum, and every continued original summand has its proved exact real value. -/
theorem OrderDisk.kernel_real {a0 b : ℝ} (D : OrderDisk a0) (hb : -1<b)
    (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤D.radius) {t s : ℝ}
    (ht : t∈Icc 0 (1/2)) (hs : s∈Icc 0 (1/2)) :
    D.kernel (b:ℂ) t s=(jacobi.GelfandLevitan.kernel b hb t s:ℂ) := by
  rw [OrderDisk.kernel,jacobi.GelfandLevitan.kernel,_root_.Complex.ofReal_tsum]
  exact tsum_congr (fun k => D.kernelTerm_real hb hbd k ht hs)

end
end jacobi.Analytic
