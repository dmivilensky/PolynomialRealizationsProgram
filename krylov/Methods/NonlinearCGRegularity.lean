import krylov.Methods.NonlinearCG
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Article: main_krylov, cor:lm and s3:cor:qn, primitive nonlinear CG coefficient regularity.
Use: prove genuine observed Hestenes--Stiefel and Hager--Zhang coefficient
regularity at every order on the actual nonzero denominator domain, then
derive its strict positivity from the true nonstagnating quadratic run.
Source: HestenesStiefel52 and HagerZhang05, actual CG orthogonality and
mathlib inner-product and reciprocal C-r calculus.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {r : WithTop ℕ∞}

/-- The genuine observed Hestenes--Stiefel scalar rule is C-r on its true denominator domain.
Use: The genuine observed Hestenes--Stiefel scalar rule is C-r on its true denominator domain.
Article: main_krylov, cor:lm and s3:cor:qn, primitive nonlinear CG coefficient regularity.
Proof: Use real smooth inner products and division by the actual nonzero observed curvature pairing. -/
theorem hsCoefficient_contDiffAt (gnew gold d : X → E) (x : X)
    (hn : ContDiffAt ℝ r gnew x) (ho : ContDiffAt ℝ r gold x) (hd : ContDiffAt ℝ r d x)
    (hden : inner ℝ (d x) (gnew x-gold x)≠0) :
    ContDiffAt ℝ r (fun p => hsCoefficient (gnew p) (gold p) (d p)) x :=
  (hn.inner ℝ (hn.sub ho)).div (hd.inner ℝ (hn.sub ho)) hden

/-- The genuine observed Hager--Zhang scalar rule is C-r on its true denominator domain.
Use: The genuine observed Hager--Zhang scalar rule is C-r on its true denominator domain.
Article: main_krylov, cor:lm and s3:cor:qn, primitive nonlinear CG coefficient regularity.
Proof: Write the real squared secant norm as its genuine inner product, so every actual scalar and vector operation is smooth. -/
theorem hzCoefficient_contDiffAt (gnew gold d : X → E) (x : X)
    (hn : ContDiffAt ℝ r gnew x) (ho : ContDiffAt ℝ r gold x) (hd : ContDiffAt ℝ r d x)
    (hden : inner ℝ (d x) (gnew x-gold x)≠0) :
    ContDiffAt ℝ r (fun p => hzCoefficient (gnew p) (gold p) (d p)) x := by
  let y := fun p => gnew p-gold p
  have hy : ContDiffAt ℝ r y x := hn.sub ho
  have ha : ContDiffAt ℝ r (fun p => 2*inner ℝ (y p) (y p)/inner ℝ (d p) (y p)) x :=
    (contDiffAt_const.mul (hy.inner ℝ hy)).div (hd.inner ℝ hy) hden
  have h := ((hy.sub (ha.smul hd)).inner ℝ hn).div (hd.inner ℝ hy) hden
  convert! h using 1
  funext p
  simp only [hzCoefficient,real_inner_self_eq_norm_sq,y,Pi.div_apply,Pi.smul_apply']

/-- The actual Hestenes--Stiefel/Hager--Zhang denominator is strictly positive at every true nonzero quadratic CG gradient.
Use: The actual Hestenes--Stiefel/Hager--Zhang denominator is strictly positive at every true nonzero quadratic CG gradient.
Article: main_krylov, cor:lm and s3:cor:qn, primitive nonlinear CG coefficient regularity.
Proof: The genuine next gradient is orthogonal to the actual previous direction, whose true search pairing is minus the positive residual energy. -/
theorem nonlinearCG_reference_denominator (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : CG.gradient Q g k≠0) :
    0 < inner ℝ (CG.direction Q g k) (CG.gradient Q g (k+1)-CG.gradient Q g k) := by
  -- The true nonzero current residual certifies the entire actual preceding nonstagnating prefix.
  have hpre : ∀ i < k, CG.gradient Q g i≠0 := by
    intro i hi hz
    exact hg (CG.gradient_eq_zero_of_le Q g hz hi.le)
  have hinv := CG.invariant Q hQ hpos g k hpre
  have hstep := CG.invariant_succ Q hQ hpos g k hinv hg
  rw [inner_sub_right,hstep.old_direction k (Nat.lt_succ_self k),hinv.search_pair,zero_sub,neg_neg]
  exact sq_pos_of_pos (norm_pos_iff.mpr hg)
end
end krylov.Methods
