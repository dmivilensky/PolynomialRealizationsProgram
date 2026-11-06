import nesterov.IQC.KYP.Lyapunov

/-! Uniform upper bounds on the actual finite-state Lyapunov expression. -/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators InnerProductSpace
open polyak.General.IQC polyak.Energy polyak.Interpolation

def windowEnergy {E : Type*} [NormedAddCommGroup E] (N : ℕ) (w : ℕ→E) (k : ℕ) : ℝ:=
  ∑ j : Fin N,‖w (k+j.val)‖^2

def matrixMass {I : Type*} [Fintype I] [DecidableEq I] (W : Bilinear (I→ℝ)) : ℝ:=
  ∑ i,∑ j,|bilinearMatrix W i j|

theorem matrixMass_nonneg {I : Type*} [Fintype I] [DecidableEq I] (W : Bilinear (I→ℝ)) : 0≤matrixMass W:=
  Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>abs_nonneg _))

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tensorForm_abs_bound {I : Type*} [Fintype I] [DecidableEq I]
    (W : Bilinear (I→ℝ)) (x : I→E) :
    |tensorForm W x x|≤matrixMass W*(∑ j,‖x j‖^2) := by
  unfold tensorForm matrixInner matrixMass
  calc
    _≤∑ i,|∑ j,bilinearMatrix W i j*inner ℝ (x i) (x j)|:=Finset.abs_sum_le_sum_abs _ _
    _≤∑ i,∑ j,|bilinearMatrix W i j*inner ℝ (x i) (x j)|:=
      Finset.sum_le_sum (fun i _=>Finset.abs_sum_le_sum_abs _ _)
    _≤∑ i,∑ j,|bilinearMatrix W i j| *(∑ k,‖x k‖^2):=by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hi:=Finset.single_le_sum (fun k _=>sq_nonneg ‖x k‖) (Finset.mem_univ i)
      have hj:=Finset.single_le_sum (fun k _=>sq_nonneg ‖x k‖) (Finset.mem_univ j)
      have hh:=abs_inner_le_half_sq (x i) (x j)
      linarith
    _=_:=by simp only [Finset.sum_mul]

/-- Fixed gain for the actual quadratic part, with all discount scalings included. -/
def quadraticGain {N : ℕ} (W : Bilinear (Fin N→ℝ)) (t : ℝ) : ℝ:=
  Real.exp (-2*t)*matrixMass W*Real.exp (2*(N:ℝ)*|t|)

theorem quadraticGain_nonneg {N : ℕ} (W : Bilinear (Fin N→ℝ)) (t : ℝ) : 0≤quadraticGain W t:=
  mul_nonneg (mul_nonneg (Real.exp_pos _).le (matrixMass_nonneg W)) (Real.exp_pos _).le

theorem sourceQuadratic_bound {N : ℕ} (W : Bilinear (Fin N→ℝ)) (t : ℝ) (w : ℕ→E) (k : ℕ) :
    |sourceQuadratic W t w k|≤quadraticGain W t*windowEnergy N w k := by
  have henergy : (∑ j : Fin N,‖Real.exp (-(j.val:ℝ)*t) • w (k+j.val)‖^2)≤
      Real.exp (2*(N:ℝ)*|t|)*windowEnergy N w k := by
    rw [windowEnergy,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow,←Real.exp_nat_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have hj0 : (0:ℝ)≤j.val:=Nat.cast_nonneg _
    have hj : (j.val:ℝ)≤N:=by exact_mod_cast j.isLt.le
    have ht : -t≤|t|:=neg_le_abs t
    push_cast
    nlinarith [mul_nonneg hj0 (sub_nonneg.mpr ht),mul_nonneg (sub_nonneg.mpr hj) (abs_nonneg t)]
  unfold sourceQuadratic
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  have hh:=mul_le_mul_of_nonneg_left (tensorForm_abs_bound W
    (fun j=>Real.exp (-(j.val:ℝ)*t) • w (k+j.val))) (Real.exp_pos (-2*t)).le
  have hm:=mul_le_mul_of_nonneg_left henergy
    (mul_nonneg (Real.exp_pos (-2*t)).le (matrixMass_nonneg W))
  exact hh.trans (by simpa only [quadraticGain,mul_assoc] using hm)

variable [CompleteSpace E]

/-- Genuine normalized potentials have the required global half-energy bound. -/
theorem normalized_value_bound {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ) (x : E) :
    |ψ x|≤‖x‖^2/2 := by
  have ht:=hψ.tableFeasible (fun i : Option E=>i.elim 0 id)
  have hh:=table_abs_value_le_half_sq ht none rfl hψ.gradient_zero hψ.value_zero (some x)
  have he : |ψ x|≤(1/2:ℝ)*‖x‖^2 := by simpa only [Option.elim_some,id_eq] using hh
  linarith

end Hilbert
end
end nesterov.IQC.KYP

namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
open nesterov.IQC nesterov.IQC.KYP polyak.General.IQC polyak.Energy
variable (A : StationaryMethod)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every query in a finite horizon is controlled by its complete latent window. -/
theorem query_sq_le_window {N : ℕ} (w : ℕ→E) (k j : ℕ) (hj : j+A.memory≤N) :
    ‖A.query w (k+j)‖^2≤A.queryGain^2*windowEnergy N w k := by
  let B:=Real.sqrt (windowEnergy N w k)
  have hB : 0≤B:=Real.sqrt_nonneg _
  have hBs : B^2=windowEnergy N w k:=Real.sq_sqrt (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
  have hnorm (l : Fin A.memory) : ‖w ((k+j)+l.val)‖≤B := by
    have hidx : j+l.val<N:=by have :=l.isLt; omega
    have hs:=Finset.single_le_sum (fun (i : Fin N) _=>sq_nonneg ‖w (k+i.val)‖)
      (Finset.mem_univ (⟨j+l.val,hidx⟩:Fin N))
    have he : k+(j+l.val)=(k+j)+l.val:=by omega
    rw [he] at hs
    change ‖w ((k+j)+l.val)‖^2≤windowEnergy N w k at hs
    nlinarith [norm_nonneg (w ((k+j)+l.val))]
  have hh : ‖A.query w (k+j)‖≤A.queryGain*B := by
    calc
      _≤∑ l : Fin A.memory,‖A.queryCoeff l • w ((k+j)+l.val)‖:=norm_sum_le _ _
      _=∑ l : Fin A.memory,|A.queryCoeff l| *‖w ((k+j)+l.val)‖:=by simp only [norm_smul,Real.norm_eq_abs]
      _≤∑ l : Fin A.memory,|A.queryCoeff l| *B:=
        Finset.sum_le_sum (fun l _=>mul_le_mul_of_nonneg_left (hnorm l) (abs_nonneg _))
      _=A.queryGain*B:=by rw [←Finset.sum_mul]; rfl
  have hs:=(sq_le_sq₀ (norm_nonneg _) (mul_nonneg A.queryGain_nonneg hB)).mpr hh
  rw [mul_pow,hBs] at hs
  exact hs

variable [CompleteSpace E]

/-- An explicit upper gain for the actual Lyapunov form. -/
def lyapunovUpper {μ L t : ℝ} {M : ℕ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    (W : Bilinear (Fin (A.memory+M)→ℝ)) : ℝ:=
  1+quadraticGain W t+potentialBound cert*(potentialHorizon cert)*A.queryGain^2

theorem lyapunovUpper_pos {μ L t : ℝ} {M : ℕ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    (W : Bilinear (Fin (A.memory+M)→ℝ)) : 0<A.lyapunovUpper cert W := by
  have hq:=quadraticGain_nonneg W t
  have hp:=potentialBound_nonneg cert
  unfold lyapunovUpper
  positivity

theorem lyapunov_abs_bound {μ L t : ℝ} {M : ℕ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    (hM : ∀ n∈cert.lags,n≤M) (W : Bilinear (Fin (A.memory+M)→ℝ))
    {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ) (w : ℕ→E) (k : ℕ) :
    |A.lyapunov cert W ψ w k|≤A.lyapunovUpper cert W*windowEnergy (A.memory+M) w k := by
  have hH : potentialHorizon cert≤M:=Finset.sup_le hM
  have hsum : (∑ j∈Finset.range (potentialHorizon cert),‖A.query w (k+j)‖^2)≤
      (potentialHorizon cert)*A.queryGain^2*windowEnergy (A.memory+M) w k := by
    calc
      _≤∑ _j∈Finset.range (potentialHorizon cert),A.queryGain^2*windowEnergy (A.memory+M) w k:=by
        apply Finset.sum_le_sum
        intro j hj
        apply A.query_sq_le_window w k j
        have :=Finset.mem_range.mp hj
        omega
      _=_:=by simp; ring
  have hp:=sourcePotential_bound cert (h:=fun n=>ψ (A.query w n))
    (b:=fun n=>‖A.query w n‖^2) (fun _=>sq_nonneg _) (fun n=>normalized_value_bound hψ _) k
  have hp':=hp.trans (mul_le_mul_of_nonneg_left hsum (potentialBound_nonneg cert))
  rw [A.lyapunov_form]
  have hq:=sourceQuadratic_bound W t w k
  have hs:=abs_sub_le (sourceQuadratic W t w k) 0 (sourcePotential cert (fun n=>ψ (A.query w n)) k)
  simp only [sub_zero,zero_sub,abs_neg] at hs
  have hm : 0≤windowEnergy (A.memory+M) w k:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  unfold lyapunovUpper
  nlinarith

end
end nesterov.StationaryMethod
