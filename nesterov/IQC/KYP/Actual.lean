import nesterov.IQC.KYP.Window
import nesterov.IQC.KYP.Potential
import polyak.Energy.Trajectory

/-! The KYP supply is the literal interpolation certificate on actual queries. -/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators
open polyak.General.IQC polyak.Energy polyak.Interpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Polynomial filtering and trajectory discounting commute exactly. -/
theorem discounted_filter_eval {d : ℕ} (v : Fin d→ℝ) (t : ℝ) (w : ℕ→E) (k : ℕ) :
    filterEval (coefficientFilter (fun j=>v j*Real.exp (j.val*t)))
      (zeroExtend (discountedPosition w t)) k=
        Real.exp (-(k*t)) • ∑ j,v j • w (k+j.val) := by
  rw [filterEval_coefficientFilter,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (k:ℤ)+(j.val:ℤ)=((k+j.val:ℕ):ℤ) by omega,zeroExtend_nat]
  simp only [discountedPosition,smul_smul]
  congr 1
  rw [mul_assoc,exp_mul_discount]
  ring

variable [CompleteSpace E]

/-- Every certificate sign is a genuine global interpolation inequality, on
arbitrary queries rather than only on a special recursion. -/
theorem actual_certificateSlack_nonneg {a : nesterov.Spectral.SymbolPair} {t : ℝ}
    (cert : nesterov.Duality.StrictCertificate a t) {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ)
    (q : ℕ→E) (k : ℕ) :
    0≤certificateSlack (transported cert) (discountedPosition q t)
      (discountedPosition (fun n=>gradient ψ (q n)) t)
      (discountedValues t (fun n=>ψ (q n))) k := by
  apply polyak.Energy.certificateSlack_nonneg
  · intro n _
    have hh:=abs_le.mp (hψ.tableFeasible q k (k+n))
    have he:=discounted_pair_slack q (fun n=>gradient ψ (q n)) (fun n=>ψ (q n)) t 1 k n
    simp only [one_mul] at he
    rw [show discountedValues t (fun n=>ψ (q n))=discountedValue (fun n=>ψ (q n)) t from rfl]
    rw [he]
    exact mul_nonneg (Real.exp_pos _).le (by linarith [hh.1])
  · intro n _
    have hh:=abs_le.mp (hψ.tableFeasible q k (k+n))
    have he:=discounted_pair_slack q (fun n=>gradient ψ (q n)) (fun n=>ψ (q n)) t (-1) k n
    simp only [neg_one_mul,←sub_eq_add_neg] at he
    rw [show discountedValues t (fun n=>ψ (q n))=discountedValue (fun n=>ψ (q n)) t from rfl]
    rw [he]
    exact mul_nonneg (Real.exp_pos _).le (by linarith [hh.2])
  · have ht:=hψ.tableFeasible (fun i : Option ℕ=>i.elim 0 q)
    have hh:=abs_le.mp (ht none (some k))
    have he:=star_slack_eq (fun i : Option ℕ=>i.elim 0 q)
      (fun i : Option ℕ=>gradient ψ (i.elim 0 q))
      (fun i : Option ℕ=>ψ (i.elim 0 q)) none (some k) rfl hψ.gradient_zero hψ.value_zero 1
    simp only [Option.elim_some,one_mul] at he
    have hn : 0≤starQuadratic 1 (q k) (gradient ψ (q k))+ψ (q k):=by linarith [hh.1]
    have hd:=discounted_star_slack q (fun n=>gradient ψ (q n)) (fun n=>ψ (q n)) t 1 k
    simp only [one_mul] at hd
    rw [show discountedValues t (fun n=>ψ (q n))=discountedValue (fun n=>ψ (q n)) t from rfl,hd]
    exact mul_nonneg (Real.exp_pos _).le hn
  · have ht:=hψ.tableFeasible (fun i : Option ℕ=>i.elim 0 q)
    have hh:=abs_le.mp (ht none (some k))
    have he:=star_slack_eq (fun i : Option ℕ=>i.elim 0 q)
      (fun i : Option ℕ=>gradient ψ (i.elim 0 q))
      (fun i : Option ℕ=>ψ (i.elim 0 q)) none (some k) rfl hψ.gradient_zero hψ.value_zero (-1)
    simp only [Option.elim_some,neg_one_mul,←sub_eq_add_neg] at he
    have hn : 0≤starQuadratic (-1) (q k) (gradient ψ (q k))-ψ (q k):=by linarith [hh.2]
    have hd:=discounted_star_slack q (fun n=>gradient ψ (q n)) (fun n=>ψ (q n)) t (-1) k
    simp only [neg_one_mul,←sub_eq_add_neg] at hd
    rw [show discountedValues t (fun n=>ψ (q n))=discountedValue (fun n=>ψ (q n)) t from rfl,hd]
    exact mul_nonneg (Real.exp_pos _).le hn

end
end nesterov.IQC.KYP

namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
open nesterov.IQC nesterov.IQC.KYP polyak.General.IQC polyak.Energy
variable (A : StationaryMethod)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The full polynomial kernel on an actual discounted latent history equals
the quadratic part of the actual interpolation certificate. -/
theorem polynomialKernel_actual {μ L t : ℝ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    {ψ : E→ℝ} (w : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (A.memory+1),A.normalizedCoeff μ L j • w (k+j))=
      gradient ψ (A.query w k)) (k : ℕ) :
    kernelEval (A.polynomialKernel cert) (zeroExtend (discountedPosition w t)) k=
      certificateQuadratic (transported cert) (discountedPosition (A.query w) t)
        (discountedPosition (fun n=>gradient ψ (A.query w n)) t) k := by
  have hq (n : ℕ) : filterEval (A.queryFilter t) (zeroExtend (discountedPosition w t)) n=
      discountedPosition (A.query w) t n:=discounted_filter_eval A.queryCoeff t w n
  have hp (n : ℕ) : filterEval (A.normalizedFilter μ L t) (zeroExtend (discountedPosition w t)) n=
      discountedPosition (fun n=>gradient ψ (A.query w n)) t n := by
    change filterEval (coefficientFilter (fun j=>A.normalizedCoeff μ L j*Real.exp (j.val*t)))
      (zeroExtend (discountedPosition w t)) n=_
    rw [discounted_filter_eval,hw]
    rfl
  rw [polynomialKernel,twoFilterKernel_eval]
  unfold zCertificateQuadratic certificateQuadratic
  simp only [transported_lags,transported_α,transported_β,transported_γplus,transported_γminus]
  rw [hq k,hp k]
  congr 2
  apply Finset.sum_congr rfl
  intro n _
  rw [show (k:ℤ)+(n:ℤ)=((k+n:ℕ):ℤ) by omega,hq (k+n),hp (k+n)]

end
end nesterov.StationaryMethod
