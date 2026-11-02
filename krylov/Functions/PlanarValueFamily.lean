import krylov.Functions.ValueFibreTranscript
import krylov.Tensor.BinaryGlobalMinimax

/-!
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii), the full actual
four-coefficient cubic function family.
Use: prescribe the source quadratic perturbation for every genuine binary
tensor; prove that fixing the observed coefficients gives exactly the
previously proved invisible value-gradient cubic difference.
Source: Appendix G, Q00=-Ap/2, Q01=-Bp/2, Q11=-Cp-D(rp)/2.
-/

namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complete actual cubic perturbation with its prescribed quadratic
terms. A common reference quadratic and linear term may be added freely.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
def planarValueFamily (φ ψ : E →L[ℝ] ℝ) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : E) : ℝ :=
  t.t0/6*(φ x)^3+t.t1/2*(φ x)^2*ψ x+t.t2/2*φ x*(ψ x)^2+t.t3/6*(ψ x)^3-
    t.t0*p/4*(φ x)^2-t.t1*p/2*φ x*ψ x-t.t2*p/2*(ψ x)^2-t.t3*r*p/4*(ψ x)^2

/-- The full family is genuinely smooth to every finite order.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
theorem planarValueFamily_contDiff (φ ψ : E →L[ℝ] ℝ) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (n : ℕ) : ContDiff ℝ n (planarValueFamily φ ψ p r t) := by
  unfold planarValueFamily
  fun_prop

/-- The actual scalar differential field of the whole four-coefficient family.
Article: main_krylov, prop:Fcycle(iii). -/
def planarValueDerivative (φ ψ : E →L[ℝ] ℝ) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (x : E) : E →L[ℝ] ℝ :=
  (t.t0/2*(φ x)^2+t.t1*φ x*ψ x+t.t2/2*(ψ x)^2-t.t0*p/2*φ x-t.t1*p/2*ψ x) • φ+
  (t.t1/2*(φ x)^2+t.t2*φ x*ψ x+t.t3/2*(ψ x)^2-t.t1*p/2*φ x-
    t.t2*p*ψ x-t.t3*r*p/2*ψ x) • ψ

/-- The displayed differential genuinely differentiates the full family.
Article: main_krylov, prop:Fcycle(iii).
Proof: differentiate the actual cubic and quadratic coordinate monomials. -/
theorem planarValueFamily_hasFDerivAt (φ ψ : E →L[ℝ] ℝ) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x : E) :
    HasFDerivAt (planarValueFamily φ ψ p r t) (planarValueDerivative φ ψ p r t x) x := by
  have hφ := φ.hasFDerivAt (x := x)
  have hψ := ψ.hasFDerivAt (x := x)
  have hA := (hφ.pow 3).const_mul (t.t0/6)
  have hB := ((hφ.pow 2).mul hψ).const_mul (t.t1/2)
  have hC := (hφ.mul (hψ.pow 2)).const_mul (t.t2/2)
  have hD := (hψ.pow 3).const_mul (t.t3/6)
  have hQa := (hφ.pow 2).const_mul (t.t0*p/4)
  have hQb := (hφ.mul hψ).const_mul (t.t1*p/2)
  have hQc := (hψ.pow 2).const_mul (t.t2*p/2)
  have hQd := (hψ.pow 2).const_mul (t.t3*r*p/4)
  have h := ((((((hA.add hB).add hC).add hD).sub hQa).sub hQb).sub hQc).sub hQd
  convert! h using 1
  · ext y
    simp only [planarValueFamily,Pi.add_apply,Pi.sub_apply,Pi.mul_apply]
    ring
  · ext v
    simp only [planarValueDerivative,add_apply,sub_apply,smul_apply,smul_eq_mul,
      Nat.reduceSub,pow_one,nsmul_eq_mul]
    ring

/-- Fixing the three genuine observations makes the exact scalar difference
of two actual full-family functions equal the invisible cubic fibre.
Article: main_krylov, prop:Fcycle(iii), Delta f=(Delta C/2)Y(X-p)(Y-rX). -/
theorem planarValueFamily_difference (φ ψ : E →L[ℝ] ℝ) (p r : ℝ)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe r t=observe r u) (x : E) :
    planarValueFamily φ ψ p r u x-planarValueFamily φ ψ p r t x=
      valueFibreCubic φ ψ (u.t2-t.t2) p r x := by
  have h0 : t.t0=u.t0 := congrArg Observation.t0 hobs
  have h3 : t.t3=u.t3 := congrArg Observation.t3 hobs
  have hP : t.t1+r*t.t2=u.t1+r*u.t2 := congrArg Observation.P hobs
  unfold planarValueFamily valueFibreCubic
  rw [h0,h3]
  linear_combination -((φ x)^2*ψ x/2-p*φ x*ψ x/2)*hP

/-- The full-family difference identity holds as equality of actual functions.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planarValueFamily_eq_add_fibre (φ ψ : E →L[ℝ] ℝ) (p r : ℝ)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe r t=observe r u) :
    planarValueFamily φ ψ p r u=fun x => planarValueFamily φ ψ p r t x+
      valueFibreCubic φ ψ (u.t2-t.t2) p r x := by
  funext x
  have h := planarValueFamily_difference φ ψ p r t u hobs x
  linarith

/-- Equal binary observations give exactly equal actual values and true
first differentials at every observed planar sample.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planarValueFamily_sample_equal (φ ψ : E →L[ℝ] ℝ) (p r : ℝ)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe r t=observe r u) (x : E)
    (hx : (φ x=0 ∧ ψ x=0) ∨ (φ x=p ∧ ψ x=0) ∨ (φ x=p ∧ ψ x=r*p)) :
    planarValueFamily φ ψ p r u x=planarValueFamily φ ψ p r t x ∧
      planarValueDerivative φ ψ p r u x=planarValueDerivative φ ψ p r t x := by
  have hzero := valueFibreCubic_sample_zero φ ψ (u.t2-t.t2) p r x hx
  have hfunc := planarValueFamily_eq_add_fibre φ ψ p r t u hobs
  constructor
  · rw [hfunc]
    change planarValueFamily φ ψ p r t x+valueFibreCubic φ ψ (u.t2-t.t2) p r x=_
    rw [hzero.1,add_zero]
  · have hd : HasFDerivAt (planarValueFamily φ ψ p r u) (planarValueDerivative φ ψ p r t x) x := by
      rw [hfunc]
      simpa only [add_zero] using! (planarValueFamily_hasFDerivAt φ ψ p r t x).add hzero.2
    exact (planarValueFamily_hasFDerivAt φ ψ p r u x).unique hd

/-- The whole actual first/last line restrictions are identical whenever
three binary observations agree.
Article: main_krylov, prop:Fcycle(iii), including exact line-search objectives. -/
theorem planarValueFamily_search_equal (φ ψ : E →L[ℝ] ℝ) (p r : ℝ)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe r t=observe r u) (a s : E)
    (hline : (ψ a=0 ∧ ψ s=0) ∨ (φ a=p ∧ φ s=0)) :
    (fun α : ℝ => planarValueFamily φ ψ p r u (a+α • s))=
      (fun α : ℝ => planarValueFamily φ ψ p r t (a+α • s)) := by
  rw [planarValueFamily_eq_add_fibre φ ψ p r t u hobs]
  exact add_valueFibreCubic_search_line _ φ ψ _ p r a s hline

end
end krylov.Functions
