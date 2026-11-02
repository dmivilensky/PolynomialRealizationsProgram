import krylov.Functions.PlanarValueFamily
import krylov.Functions.SegmentHessian

/-!
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii), actual differential
and operator dictionary for the full binary cubic function family.
Use: prove its affine Hessian and constant third tensor, not merely equality
of formal observations, and compute the genuine final Hessian compression.
Source: the prescribed quadratic perturbation and exact polynomial calculus.
-/

namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic chebyshev1.Nonlinear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine affine Hessian field of the complete actual planar family.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
def planarValueHessian (φ ψ : E →L[ℝ] ℝ) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (t.t0*φ x+t.t1*ψ x-t.t0*p/2) • φ.smulRight φ+
  (t.t1*φ x+t.t2*ψ x-t.t1*p/2) • (φ.smulRight ψ+ψ.smulRight φ)+
  (t.t2*φ x+t.t3*ψ x-t.t2*p-t.t3*r*p/2) • ψ.smulRight ψ

/-- The true first differential differentiates to the displayed affine Hessian.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
theorem planarValueDerivative_hasFDerivAt (φ ψ : E →L[ℝ] ℝ) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x : E) :
    HasFDerivAt (planarValueDerivative φ ψ p r t) (planarValueHessian φ ψ p r t x) x := by
  have hφ := φ.hasFDerivAt (x := x)
  have hψ := ψ.hasFDerivAt (x := x)
  have hA := (((((hφ.pow 2).const_mul (t.t0/2)).add ((hφ.mul hψ).const_mul t.t1)).add
    ((hψ.pow 2).const_mul (t.t2/2))).sub (hφ.const_mul (t.t0*p/2))).sub
    (hψ.const_mul (t.t1*p/2))
  have hB := ((((((hφ.pow 2).const_mul (t.t1/2)).add ((hφ.mul hψ).const_mul t.t2)).add
    ((hψ.pow 2).const_mul (t.t3/2))).sub (hφ.const_mul (t.t1*p/2))).sub
    (hψ.const_mul (t.t2*p))).sub (hψ.const_mul (t.t3*r*p/2))
  have h := (hA.smul_const φ).add (hB.smul_const ψ)
  convert! h using 1
  · ext y v
    simp only [planarValueDerivative,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,
      add_apply,smul_apply,smul_eq_mul]
    ring
  · ext v w
    simp only [planarValueHessian,add_apply,sub_apply,smul_apply,smul_eq_mul,
      ContinuousLinearMap.smulRight_apply,Nat.reduceSub,pow_one,nsmul_eq_mul]
    ring

/-- The genuine constant third differential of the complete planar cubic family.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
def planarValueThird (φ ψ : E →L[ℝ] ℝ) (t : krylov.Tensor.BinaryCubic) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := by
  letI : AddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup (R := ℝ) (R₂ := ℝ) (M := E) (M₂ := E →L[ℝ] E →L[ℝ] ℝ)
  exact (t.t0 • φ+t.t1 • ψ).smulRight (φ.smulRight φ)+
    (t.t1 • φ+t.t2 • ψ).smulRight (φ.smulRight ψ+ψ.smulRight φ)+
    (t.t2 • φ+t.t3 • ψ).smulRight (ψ.smulRight ψ)

/-- Differentiating the actual affine Hessian gives the prescribed third tensor.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
theorem planarValueHessian_hasFDerivAt (φ ψ : E →L[ℝ] ℝ) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x : E) :
    HasFDerivAt (planarValueHessian φ ψ p r t) (planarValueThird φ ψ t) x := by
  have : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  have hφ := φ.hasFDerivAt (x := x)
  have hψ := ψ.hasFDerivAt (x := x)
  have hA := ((hφ.const_mul t.t0).add (hψ.const_mul t.t1)).sub_const (t.t0*p/2)
  have hB := ((hφ.const_mul t.t1).add (hψ.const_mul t.t2)).sub_const (t.t1*p/2)
  have hC := (((hφ.const_mul t.t2).add (hψ.const_mul t.t3)).sub_const (t.t2*p)).sub_const (t.t3*r*p/2)
  have h := ((hA.smul_const (φ.smulRight φ)).add
    (hB.smul_const (φ.smulRight ψ+ψ.smulRight φ))).add (hC.smul_const (ψ.smulRight ψ))
  convert! h using 1

/-- Exact scalar evaluation of the constant third differential.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
theorem planarValueThird_apply (φ ψ : E →L[ℝ] ℝ) (t : krylov.Tensor.BinaryCubic)
    (u v w : E) :
    planarValueThird φ ψ t u v w=
      t.t0*φ u*φ v*φ w+t.t1*(φ u*φ v*ψ w+φ u*ψ v*φ w+ψ u*φ v*φ w)+
      t.t2*(φ u*ψ v*ψ w+ψ u*φ v*ψ w+ψ u*ψ v*φ w)+t.t3*ψ u*ψ v*ψ w := by
  simp only [planarValueThird,add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.smulRight_apply]
  ring

/-- The genuine affine Hessian is exactly its midpoint average.
Article: main_krylov, thm:Fplanar, actual secant dictionary. -/
theorem planarValueHessian_average (φ ψ : E →L[ℝ] ℝ) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (a s : E) :
    averagedDerivative (planarValueHessian φ ψ p r t) a s=
      planarValueHessian φ ψ p r t (a+(1/2 : ℝ) • s) := by
  let H0 := planarValueHessian φ ψ p r t 0
  let T := planarValueThird φ ψ t
  have he (x : E) : planarValueHessian φ ψ p r t x=H0+T x := by
    ext v w
    simp only [H0,T,planarValueHessian,planarValueThird,map_zero,
      add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.smulRight_apply]
    ring
  rw [show planarValueHessian φ ψ p r t=(fun x => H0+T x) from funext he]
  exact averagedHessian_affine H0 T a s

/-- The actual final Hessian compresses to the full matrix in the source,
with all four coefficients and the actual reference step lengths.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
theorem planarValueHessian_final_matrix (φ ψ : E →L[ℝ] ℝ) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x : E) (hφ : φ x=p) (hψ : ψ x=r*p)
    (e h : E) (hφe : φ e=1) (hψe : ψ e=0) (hφh : φ h=0) (hψh : ψ h=1) :
    let v : Fin 2 → E := ![e,h]
    compressBilinear v (planarValueHessian φ ψ p r t x)=
      (p/2) • !![t.t0+2*r*t.t1,t.t1+2*r*t.t2;t.t1+2*r*t.t2,r*t.t3] := by
  dsimp only
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compressBilinear,planarValueHessian,ContinuousLinearMap.smulRight_apply,hφ,hψ,hφe,hψe,hφh,hψh] <;> ring

end
end krylov.Functions
