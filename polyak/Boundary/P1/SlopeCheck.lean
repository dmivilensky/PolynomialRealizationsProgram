import polyak.Numerics.Parametric.DerivativeTwo

/-!
Article: Proposition P₁, exact implicit source slope bounds.
Use: all quantities checked here are enclosures of the actual AD Jacobian and
parameter derivative. Cramer's rule proves the actual u derivative is negative
and satisfies the strict reciprocal-cosh slope inequality.
-/
namespace polyak.Boundary.P1
open LeanCert.Core LeanCert.Engine Numerics.Parametric

private def slopeDeterminant (J : Matrix (Fin 2) (Fin 2) IntervalRat) : IntervalRat :=
  (J 0 0 |>.mul (J 1 1)).sub (J 0 1 |>.mul (J 1 0))

private def slopeNumeratorA (J : Matrix (Fin 2) (Fin 2) IntervalRat)
    (p : Fin 2 → IntervalRat) : IntervalRat :=
  (J 0 1 |>.mul (p 1)).sub (J 1 1 |>.mul (p 0))

private def sourceUInterval (I : IntervalRat) (X : Fin 2 → IntervalRat) : IntervalRat :=
  ((IntervalRat.singleton 1).sub (I.mul (IntervalRat.singleton (1/2)))).add
    ((I.mul I).mul (X 0))

private def sourceUDerivativeNumerator (I : IntervalRat) (X : Fin 2 → IntervalRat)
    (J : Matrix (Fin 2) (Fin 2) IntervalRat) (p : Fin 2 → IntervalRat) : IntervalRat :=
  (slopeDeterminant J |>.mul ((IntervalRat.singleton (-1/2)).add
    ((IntervalRat.singleton 2 |>.mul I).mul (X 0)))).add
      ((I.mul I).mul (slopeNumeratorA J p))

/-- Source-linked strict bounds on u_z and its exact squared physical slope. -/
def sourceSlopeCheck (F : Fin 2 → Expr) (I : IntervalRat) (X : Fin 2 → IntervalRat)
    (cfg : DyadicConfig) : Bool :=
  let J:=dyadicJacobian F I X cfg
  let p:=fun i => outcome (dyadicDerivative (F i) (finBoxEnv (box I X)) 0 cfg)
  let D:=slopeDeterminant J
  let N:=sourceUDerivativeNumerator I X J p
  let U:=sourceUInterval I X
  let R:=(((IntervalRat.singleton 1).add (U.mul U)).mul (D.mul D)).sub
    (((N.mul N).mul (I.mul I)).mul ((IntervalRat.singleton 1).sub (I.mul I)))
  dyadicJacobianSucceeded F I X cfg &&
    decide (∀ i,succeeded (dyadicDerivative (F i) (finBoxEnv (box I X)) 0 cfg)=true) &&
    decide (0<D.lo) && decide (N.hi<0) && decide (0<R.lo)

noncomputable section

/-- The complementary exact Cramer identity for the first unknown. -/
theorem cramer_A (J : Matrix (Fin 2) (Fin 2) ℝ) (p v : Fin 2 → ℝ)
    (h : J.mulVec v= -p) : determinantTwo J*v 0=J 0 1*p 1-J 1 1*p 0 := by
  have h0:=congrFun h 0
  have h1:=congrFun h 1
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.neg_apply] at h0 h1
  unfold determinantTwo
  linear_combination J 1 1*h0-J 0 1*h1

/-- The checker proves the actual branch derivative bounds, with no assumed
matrix inverse or assumed source slope substituted for the AD derivative. -/
theorem sourceSlopeCheck_sound (F : Fin 2 → Expr) (hF : ∀ i,ADSupported (F i))
    (I : IntervalRat) (X : Fin 2 → IntervalRat) (cfg : DyadicConfig)
    (hc : sourceSlopeCheck F I X cfg=true)
    {s : ℝ} {x v : Fin 2 → ℝ} (hs : s∈I) (hx : FinBoxMem x X)
    (he : (jacobian F s x).mulVec v= -parameterDerivative F s x) :
    let du:= -1/2+2*s*x 0+s^2*v 0
    du<0 ∧ du^2*s^2*(1-s^2)<1+(1-s/2+s^2*x 0)^2 := by
  simp only [sourceSlopeCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hj:=dyadicJacobian_mem F hF I X cfg hc.1.1.1.1 hs hx
  have hp:=parameterDerivative_mem F I X cfg hc.1.1.1.2 hs hx
  let J:=jacobian F s x
  let D:=determinantTwo J
  let NA:=J 0 1*parameterDerivative F s x 1-J 1 1*parameterDerivative F s x 0
  let du:= -1/2+2*s*x 0+s^2*v 0
  let U:=1-s/2+s^2*x 0
  have hd : D∈slopeDeterminant (dyadicJacobian F I X cfg) :=
    IntervalRat.mem_sub (IntervalRat.mem_mul (hj 0 0) (hj 1 1))
      (IntervalRat.mem_mul (hj 0 1) (hj 1 0))
  have hnA : NA∈slopeNumeratorA (dyadicJacobian F I X cfg)
      (fun i => outcome (dyadicDerivative (F i) (finBoxEnv (box I X)) 0 cfg)) :=
    IntervalRat.mem_sub (IntervalRat.mem_mul (hj 0 1) (hp 1))
      (IntervalRat.mem_mul (hj 1 1) (hp 0))
  have hu : U∈sourceUInterval I X := by
    unfold sourceUInterval
    have hh:=IntervalRat.mem_add
      (IntervalRat.mem_sub (IntervalRat.mem_singleton (1 : ℚ))
        (IntervalRat.mem_mul hs (IntervalRat.mem_singleton (1/2 : ℚ))))
      (IntervalRat.mem_mul (IntervalRat.mem_mul hs hs) (hx 0))
    convert hh using 1
    norm_num [U,pow_two,div_eq_mul_inv]
  have hn : D*du∈sourceUDerivativeNumerator I X (dyadicJacobian F I X cfg)
      (fun i => outcome (dyadicDerivative (F i) (finBoxEnv (box I X)) 0 cfg)) := by
    have hh:=IntervalRat.mem_add
      (IntervalRat.mem_mul hd (IntervalRat.mem_add (IntervalRat.mem_singleton (-1/2 : ℚ))
        (IntervalRat.mem_mul (IntervalRat.mem_mul (IntervalRat.mem_singleton (2 : ℚ)) hs) (hx 0))))
      (IntervalRat.mem_mul (IntervalRat.mem_mul hs hs) hnA)
    have hcr:=cramer_A J (parameterDerivative F s x) v he
    change D*v 0=NA at hcr
    convert hh using 1 <;> norm_num [sourceUDerivativeNumerator,du]
    rw [←hcr]
    ring
  have hres:=IntervalRat.mem_sub
    (IntervalRat.mem_mul (IntervalRat.mem_add (IntervalRat.mem_singleton (1 : ℚ))
      (IntervalRat.mem_mul hu hu)) (IntervalRat.mem_mul hd hd))
    (IntervalRat.mem_mul (IntervalRat.mem_mul (IntervalRat.mem_mul hn hn)
      (IntervalRat.mem_mul hs hs))
      (IntervalRat.mem_sub (IntervalRat.mem_singleton (1 : ℚ)) (IntervalRat.mem_mul hs hs)))
  norm_num only [Rat.cast_one] at hres
  have hDp : 0<D := lt_of_lt_of_le (by exact_mod_cast hc.1.1.2) hd.1
  have hNn : D*du<0 := lt_of_le_of_lt hn.2 (by exact_mod_cast hc.1.2)
  have hRn : 0<(1+U*U)*(D*D)-(D*du*(D*du)*(s*s))*(1-s*s) :=
    lt_of_lt_of_le (by exact_mod_cast hc.2) hres.1
  change du<0 ∧ du^2*s^2*(1-s^2)<1+U^2
  constructor
  · by_contra hh
    exact (not_lt_of_ge (mul_nonneg hDp.le (le_of_not_gt hh))) hNn
  · have heq : (1+U*U)*(D*D)-(D*du*(D*du)*(s*s))*(1-s*s)=
        D^2*(1+U^2-du^2*s^2*(1-s^2)) := by ring
    rw [heq] at hRn
    have hh:=(mul_pos_iff_of_pos_left (sq_pos_of_pos hDp)).mp hRn
    linarith

end
end polyak.Boundary.P1
