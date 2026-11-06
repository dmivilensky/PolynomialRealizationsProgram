import nesterov.IQC.KYP.Actual

/-!
The actual Lyapunov expression supplied by the strict finite certificate.
Its quadratic part has fixed real coefficients on the complete latent window;
its value correction is the source's finite potential correction.
-/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators InnerProductSpace
open polyak.General.IQC polyak.Energy

section Tensor
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tensorForm_common_smul (W : Bilinear (I→ℝ)) (a : ℝ) (x : I→E) :
    tensorForm W (fun j=>a • x j) (fun j=>a • x j)=a^2*tensorForm W x x := by
  unfold tensorForm matrixInner
  simp only [real_inner_smul_left,real_inner_smul_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual fixed quadratic form on the undiscounted latent window. -/
def sourceQuadratic {N : ℕ} (W : Bilinear (Fin N→ℝ)) (t : ℝ) (w : ℕ→E) (k : ℕ) : ℝ:=
  Real.exp (-2*t)*tensorForm W
    (fun j=>Real.exp (-(j.val:ℝ)*t) • w (k+j.val))
    (fun j=>Real.exp (-(j.val:ℝ)*t) • w (k+j.val))

theorem sourceQuadratic_eq_discounted {N : ℕ} (W : Bilinear (Fin N→ℝ)) (t : ℝ) (w : ℕ→E) (k : ℕ) :
    sourceQuadratic W t w k=Real.exp (2*(k:ℝ)*t-2*t)*
      tensorForm W (window N (discountedPosition w t) k) (window N (discountedPosition w t) k) := by
  have he : window N (discountedPosition w t) k=
      (fun j=>Real.exp (-((k:ℝ)*t)) • (Real.exp (-(j.val:ℝ)*t) • w (k+j.val))) := by
    funext j
    dsimp [window,discountedPosition]
    rw [smul_smul,←Real.exp_add]
    congr 2
    push_cast
    ring
  rw [he,tensorForm_common_smul]
  unfold sourceQuadratic
  have hc : Real.exp (2*(k:ℝ)*t-2*t)*(Real.exp (-((k:ℝ)*t)))^2=Real.exp (-2*t) := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    push_cast
    ring
  rw [←mul_assoc,hc]

end Tensor
end
end nesterov.IQC.KYP

namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
open nesterov.IQC nesterov.IQC.KYP polyak.General.IQC polyak.Energy
variable (A : StationaryMethod)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {μ L t : ℝ}

/-- Discounted quadratic storage minus the actual finite value boundary. -/
def discountedLyapunov {M : ℕ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    (W : Bilinear (Fin (A.memory+M)→ℝ)) (ψ : E→ℝ) (w : ℕ→E) (k : ℕ) : ℝ:=
  tensorForm W (window (A.memory+M) (discountedPosition w t) k)
    (window (A.memory+M) (discountedPosition w t) k)-
      valueBoundary cert (discountedValues t (fun n=>ψ (A.query w n))) k

/-- The actual undiscounted Lyapunov function in the article's normalization. -/
def lyapunov {M : ℕ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    (W : Bilinear (Fin (A.memory+M)→ℝ)) (ψ : E→ℝ) (w : ℕ→E) (k : ℕ) : ℝ:=
  Real.exp (2*(k:ℝ)*t-2*t)*A.discountedLyapunov cert W ψ w k

omit [CompleteSpace E] in
/-- The Lyapunov function has precisely the required form: a fixed quadratic
form on the state, minus a finite linear combination of actual potential values. -/
theorem lyapunov_form {M : ℕ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    (W : Bilinear (Fin (A.memory+M)→ℝ)) (ψ : E→ℝ) (w : ℕ→E) (k : ℕ) :
    A.lyapunov cert W ψ w k=sourceQuadratic W t w k-
      sourcePotential cert (fun n=>ψ (A.query w n)) k := by
  unfold lyapunov discountedLyapunov
  rw [mul_sub,←sourceQuadratic_eq_discounted]
  rfl

/-- The actual normalized potential discharges the supply inequality in the
constructed KYP storage on every Hilbert trajectory. -/
theorem discountedLyapunov_dissipation {M : ℕ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    (hM : ∀ n∈cert.lags,n≤M)
    (W : Bilinear (Fin (A.memory+M)→ℝ)) (η : ℝ)
    (hW : ∀ (x : Fin (A.memory+M)→ℝ) (d : ℝ),
      W (registerStep x d) (registerStep x d)-W x x+
        instantaneous (ofKernel (A.polynomialKernel cert)) x d≤
          -η*((∑ j,‖x j‖^2)+‖d‖^2))
    {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ) (w : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (A.memory+1),A.normalizedCoeff μ L j • w (k+j))=
      gradient ψ (A.query w k)) (k : ℕ) :
    A.discountedLyapunov cert W ψ w (k+1)-A.discountedLyapunov cert W ψ w k≤
      -η*(∑ j : Fin (A.memory+M+1),‖discountedPosition w t (k+j.val)‖^2) := by
  have hs:=A.polynomialKernel_supported cert hM
  have hd:=tensor_window_dissipation (ofKernel_supported hs) W η hW (discountedPosition w t) k
  have he : NatKernel.eval (ofKernel (A.polynomialKernel cert)) (discountedPosition w t) k=
      certificateQuadratic (transported cert) (discountedPosition (A.query w) t)
        (discountedPosition (fun n=>gradient ψ (A.query w n)) t) k := by
    rw [NatKernel.eval_eq_whole,ofKernel_toKernel hs]
    exact A.polynomialKernel_actual cert w hw k
  rw [he] at hd
  have hn:=actual_certificateSlack_nonneg cert hψ (A.query w) k
  rw [certificateSlack_eq,←valueBoundary_difference] at hn
  unfold discountedLyapunov
  linarith

/-- Rescaling back gives the source's strict quadratic dissipation. -/
theorem lyapunov_dissipation {M : ℕ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    (hM : ∀ n∈cert.lags,n≤M)
    (W : Bilinear (Fin (A.memory+M)→ℝ)) (η : ℝ) (hη : 0≤η)
    (hW : ∀ (x : Fin (A.memory+M)→ℝ) (d : ℝ),
      W (registerStep x d) (registerStep x d)-W x x+
        instantaneous (ofKernel (A.polynomialKernel cert)) x d≤
          -η*((∑ j,‖x j‖^2)+‖d‖^2))
    {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ) (w : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (A.memory+1),A.normalizedCoeff μ L j • w (k+j))=
      gradient ψ (A.query w k)) (k : ℕ) :
    A.lyapunov cert W ψ w (k+1)≤Real.exp (2*t)*A.lyapunov cert W ψ w k-
      (η*Real.exp (-2*(A.memory+M:ℕ)*|t|))*(∑ j : Fin (A.memory+M),‖w (k+j.val)‖^2) := by
  have hd:=A.discountedLyapunov_dissipation cert hM W η hW hψ w hw k
  have hm:=mul_le_mul_of_nonneg_left hd (Real.exp_pos (2*(k:ℝ)*t)).le
  have he1 : Real.exp (2*((k+1:ℕ):ℝ)*t-2*t)=Real.exp (2*(k:ℝ)*t) := by
    congr 1
    push_cast
    ring
  have he2 : Real.exp (2*t)*Real.exp (2*(k:ℝ)*t-2*t)=Real.exp (2*(k:ℝ)*t) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have henergy : Real.exp (2*(k:ℝ)*t)*
      (∑ j : Fin (A.memory+M+1),‖discountedPosition w t (k+j.val)‖^2)=
      ∑ j : Fin (A.memory+M+1),Real.exp (-2*j.val*t)*‖w (k+j.val)‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [norm_discountedPosition_sq]
    unfold polyak.Growth.discountedEnergy
    rw [←mul_assoc,←Real.exp_add]
    congr 2
    push_cast
    ring
  have hlower : Real.exp (-2*(A.memory+M:ℕ)*|t|)*
      (∑ j : Fin (A.memory+M),‖w (k+j.val)‖^2)≤
      ∑ j : Fin (A.memory+M+1),Real.exp (-2*j.val*t)*‖w (k+j.val)‖^2 := by
    rw [Fin.sum_univ_castSucc,Finset.mul_sum]
    apply le_trans _ (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    simp only [Fin.val_castSucc,Nat.cast_add]
    have hj : (j.val:ℝ)≤A.memory+M:=by exact_mod_cast j.isLt.le
    have hj0 : (0:ℝ)≤j.val:=Nat.cast_nonneg _
    have ht:=le_abs_self t
    nlinarith [mul_nonneg (sub_nonneg.mpr hj) (abs_nonneg t),
      mul_nonneg hj0 (sub_nonneg.mpr ht)]
  have hc:=mul_le_mul_of_nonneg_left hlower hη
  unfold lyapunov
  rw [he1,←mul_assoc,he2]
  rw [mul_sub] at hm
  have hh : Real.exp (2*(k:ℝ)*t)*(-η*
      (∑ j : Fin (A.memory+M+1),‖discountedPosition w t (k+j.val)‖^2))=
      -η*(∑ j : Fin (A.memory+M+1),Real.exp (-2*j.val*t)*‖w (k+j.val)‖^2) := by
    rw [←henergy]
    ring
  rw [hh] at hm
  nlinarith

end
end nesterov.StationaryMethod
