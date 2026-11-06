import nesterov.IQC.KYP.Data

/-! The certificate's finite Lyapunov form gives a uniform from-rest norm bound. -/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators
open polyak.General.IQC
variable {A : StationaryMethod} {μ L t : ℝ} {M : ℕ}
variable {cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t}

namespace LyapunovData
variable (D : LyapunovData A μ L t M cert)

/-- Squared window bound inherited from the actual positive Lyapunov form. -/
theorem norm_sq_bound (hμ : 0<μ) (hμL : μ<L)
    (hr : middleRadius A μ L<Real.exp t) (hM : ∀ n∈cert.lags,n≤M)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ) (w : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (A.memory+1),A.normalizedCoeff μ L j • w (k+j))=
      gradient ψ (A.query w k)) (k : ℕ) :
    ‖w k‖^2≤(D.upperConstant/D.lowerConstant)*(Real.exp (2*t)^k)*windowEnergy (A.memory+M) w 0 := by
  have hb (n : ℕ) : 0≤windowEnergy (A.memory+M) w n:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hVk (n : ℕ) : A.lyapunov cert D.matrix ψ w n≤
      Real.exp (2*t)^n*A.lyapunov cert D.matrix ψ w 0 := by
    induction n with
    | zero=>simp
    | succ n ih=>
      calc
        _≤Real.exp (2*t)*A.lyapunov cert D.matrix ψ w n-D.dissipationConstant*windowEnergy (A.memory+M) w n:=
          D.step hM hψ w hw n
        _≤Real.exp (2*t)*A.lyapunov cert D.matrix ψ w n:=
          sub_le_self _ (mul_nonneg D.dissipationConstant_pos.le (hb n))
        _≤Real.exp (2*t)*(Real.exp (2*t)^n*A.lyapunov cert D.matrix ψ w 0):=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
        _=_:=by rw [pow_succ]; ring
  have h0:= (D.comparison hμ hμL hr hM hψ w hw 0).2
  have hk:= (D.comparison hμ hμL hr hM hψ w hw k).1
  have hidx : 0<A.memory+M:=by have :=A.memory_pos; omega
  have hsingle:=Finset.single_le_sum (fun (j : Fin (A.memory+M)) _=>sq_nonneg ‖w (k+j.val)‖)
    (Finset.mem_univ (⟨0,hidx⟩:Fin (A.memory+M)))
  change ‖w (k+0)‖^2≤windowEnergy (A.memory+M) w k at hsingle
  rw [Nat.add_zero] at hsingle
  have hm:=mul_le_mul_of_nonneg_left hsingle D.lowerConstant_pos.le
  have hu:=mul_le_mul_of_nonneg_left h0 (pow_nonneg (Real.exp_pos (2*t)).le k)
  have hh:=hm.trans (hk.trans ((hVk k).trans hu))
  apply (mul_le_mul_iff_right₀ D.lowerConstant_pos).mp
  have he : D.lowerConstant*((D.upperConstant/D.lowerConstant)*(Real.exp (2*t)^k)*windowEnergy (A.memory+M) w 0)=
      Real.exp (2*t)^k*(D.upperConstant*windowEnergy (A.memory+M) w 0) := by
    field_simp [ne_of_gt D.lowerConstant_pos]
  rw [he]
  nlinarith

/-- Uniform finite-horizon growth constant for the larger initial latent window. -/
def initialWindowGain (N : ℕ) : ℝ:=∑ j : Fin N,((A.stepBound L)^j.val)^2

def restConstant : ℝ:=1+Real.sqrt
  ((D.upperConstant/D.lowerConstant)*initialWindowGain (A:=A) (L:=L) (A.memory+M)*A.memory)

theorem restConstant_pos : 0<D.restConstant := by
  unfold restConstant
  positivity

/-- The original objective class controls every initial gradient in the
extended state uniformly, so the Lyapunov norm bound has one from-rest gain. -/
theorem fromRest_norm_bound (hμ : 0<μ) (hμL : μ<L)
    (hr : middleRadius A μ L<Real.exp t) (hM : ∀ n∈cert.lags,n≤M)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E→ℝ} (hf : polyak.CenteredSmoothStronglyConvex μ L f)
    (w : ℕ→E) (hw : A.IsTrajectory (gradient f) w) (x0 : E)
    (hinit : ∀ j : Fin A.memory,w j.val=x0) (k : ℕ) :
    ‖w k‖≤D.restConstant*(Real.exp t)^k*‖x0‖ := by
  have hg (x : E) : ‖gradient f x‖≤|L| *‖x‖ := by
    have hh:=hf.grad_lipschitz x 0
    simpa only [hf.gradient_zero,sub_zero,abs_of_pos (hf.mu_pos.trans hf.mu_lt_L)] using hh
  have hwindow : windowEnergy (A.memory+M) w 0≤
      initialWindowGain (A:=A) (L:=L) (A.memory+M)*(A.stateNorm w 0)^2 := by
    unfold windowEnergy initialWindowGain
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    have hn:=A.norm_le_stateNorm w j.val A.firstIndex
    have hs:=hw.stateNorm_le A hg j.val
    have hn' : ‖w j.val‖≤(A.stepBound L)^j.val*A.stateNorm w 0 := by
      have hn0 : ‖w j.val‖≤A.stateNorm w j.val:=by
        simpa only [StationaryMethod.firstIndex,Nat.add_zero] using hn
      exact hn0.trans hs
    have hsq:=(sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg (A.stepBound_pos L).le _) (A.stateNorm_nonneg w 0))).mpr hn'
    simpa only [Nat.zero_add,mul_pow] using hsq
  have hstate : (A.stateNorm w 0)^2=(A.memory:ℝ)*‖x0‖^2 := by
    rw [A.stateNorm_sq]
    simp only [Nat.zero_add,hinit,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [hstate] at hwindow
  have hq:=D.norm_sq_bound hμ hμL hr hM hf.normalize w
    (hw.normalized A hf.differentiable) k
  have hbase : 0≤(D.upperConstant/D.lowerConstant)*initialWindowGain (A:=A) (L:=L) (A.memory+M)*A.memory := by
    have hi : 0 ≤ initialWindowGain (A:=A) (L:=L) (A.memory+M):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
    exact mul_nonneg (mul_nonneg (div_nonneg D.upperConstant_pos.le D.lowerConstant_pos.le) hi)
      (Nat.cast_nonneg _)
  have hm:=mul_le_mul_of_nonneg_left hwindow
    (mul_nonneg (div_nonneg D.upperConstant_pos.le D.lowerConstant_pos.le) (pow_nonneg (Real.exp_pos (2*t)).le k))
  have hh:=hq.trans hm
  have he : Real.exp (2*t)^k=((Real.exp t)^k)^2 := by
    rw [show Real.exp (2*t)=(Real.exp t)^2 from by rw [←Real.exp_nat_mul]; norm_num,←pow_mul,←pow_mul]
    congr 1
    omega
  have hsqrt:=Real.sq_sqrt hbase
  have hK : ((D.upperConstant/D.lowerConstant)*initialWindowGain (A:=A) (L:=L) (A.memory+M)*A.memory)≤D.restConstant^2 := by
    unfold restConstant
    nlinarith [Real.sqrt_nonneg ((D.upperConstant/D.lowerConstant)*initialWindowGain (A:=A) (L:=L) (A.memory+M)*A.memory)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg D.restConstant_pos.le (pow_nonneg (Real.exp_pos t).le k)) (norm_nonneg x0))).mp
  rw [mul_pow,mul_pow]
  rw [he] at hh
  have hp:=mul_le_mul_of_nonneg_right hK
    (mul_nonneg (sq_nonneg ((Real.exp t)^k)) (sq_nonneg ‖x0‖))
  nlinarith

end LyapunovData
end
end nesterov.IQC.KYP
