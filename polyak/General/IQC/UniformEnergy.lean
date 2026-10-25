import polyak.General.IQC.HeavyBallLoop
import polyak.General.IQC.EnergyRate

/-! Appendix D: uniformity of the actual energy estimate and the original
worst-case rate. The bound includes all normalized potentials, dimensions,
and independent initial positions. -/
noncomputable section
namespace polyak.General.IQC
open polyak Growth Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem norm_discountSequence_sq (t : ℝ) (x : ℕ → E) (k : ℕ) :
    ‖discountSequence t x k‖^2=discountedEnergy x t k := by
  rw [discountSequence,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow]
  unfold discountedEnergy
  congr 1
  rw [←Real.exp_nat_mul]
  congr 1
  ring

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem sequenceNorm_sq (x : ℕ → E) : sequenceNorm x^2=∑' k,‖x k‖^2 :=
  Real.sq_sqrt (tsum_nonneg (fun _ => sq_nonneg _))

def UniformExecutionBound (A B β t K : ℝ) : Prop :=
  ∀ d : ℕ,∀ r : Run (EuclideanSpace ℝ (Fin d)) A B β,
    SquareSummable (discountSequence t (fun k => r.x (k+1))) ∧
    sequenceNorm (discountSequence t (fun k => r.x (k+1)))≤K*(‖r.x 0‖+‖r.x 1‖)

theorem mass_le_of_discounted_l2 {A B β t K : ℝ} (hK : 0≤K) (r : Run E A B β)
    (hs : SquareSummable (discountSequence t (fun k => r.x (k+1))))
    (hn : sequenceNorm (discountSequence t (fun k => r.x (k+1)))≤K*(‖r.x 0‖+‖r.x 1‖))
    (n : ℕ) :
    mass (discountedEnergy r.x t) 0 n≤(1+2*Real.exp (-2*t)*K^2)*stateNorm r.x 0^2 := by
  let e:=fun k => r.x (k+1)
  have hsum : Summable (discountedEnergy e t):=by
    simpa only [SquareSummable,norm_discountSequence_sq] using hs
  have hsq : (∑' k,discountedEnergy e t k)≤2*K^2*stateNorm r.x 0^2:=by
    have hnormsq:=sq_le_sq₀ (sequenceNorm_nonneg (discountSequence t e))
      (mul_nonneg hK (add_nonneg (norm_nonneg _) (norm_nonneg _))) |>.mpr hn
    rw [sequenceNorm_sq] at hnormsq
    simp only [norm_discountSequence_sq] at hnormsq
    have hcross:=sq_nonneg (‖r.x 0‖-‖r.x 1‖)
    rw [stateNorm_sq]
    nlinarith [mul_nonneg (sq_nonneg K) hcross]
  have he (k : ℕ) : discountedEnergy r.x t (k+1)=Real.exp (-2*t)*discountedEnergy e t k:=by
    unfold discountedEnergy
    rw [←mul_assoc,←Real.exp_add]
    congr 2
    push_cast
    ring
  cases n with
  | zero => simp only [mass,Ico_self,sum_empty]; positivity
  | succ n =>
    change (∑ k∈Ico 0 (n+1),discountedEnergy r.x t k)≤_
    rw [Nat.Ico_zero_eq_range,sum_range_succ']
    simp only [discountedEnergy,Nat.cast_zero,mul_zero,zero_mul,Real.exp_zero,one_mul]
    change (∑ k∈range n,discountedEnergy r.x t (k+1))+‖r.x 0‖^2≤_
    simp_rw [he]
    rw [←mul_sum]
    have hh:=hsum.sum_le_tsum (range n) (fun _ _ => discountedEnergy_nonneg e t _)
    have hm:=mul_le_mul_of_nonneg_left (hh.trans hsq) (Real.exp_pos (-2*t)).le
    have hleft:=norm_left_le_stateNorm r.x 0
    have hleftsq:=pow_le_pow_left₀ (norm_nonneg _) hleft 2
    nlinarith

theorem uniformMassBound_of_execution {A B β t K : ℝ} (hK : 0≤K)
    (h : UniformExecutionBound A B β t K) :
    UniformMassBound A B β t (1+2*Real.exp (-2*t)*K^2) := by
  intro d r n
  exact mass_le_of_discounted_l2 hK r (h d r).1 (h d r).2 n

theorem strict_growth_of_execution {A B β t K : ℝ} (hB : B≠0) (hK : 0≤K)
    (h : UniformExecutionBound A B β t K) : growthRate A B β<Real.exp t :=
  growthRate_lt_exp_of_uniformMassBound hB (by positivity) (uniformMassBound_of_execution hK h)

end polyak.General.IQC
