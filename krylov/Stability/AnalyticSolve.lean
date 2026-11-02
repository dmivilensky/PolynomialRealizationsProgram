import krylov.Stability.AnalyticCG
import krylov.Methods.SecantSolve

/-!
Article: main_krylov, def:classes and lem:U, genuine computed coefficient regularity.
Use: prove local analyticity of the implemented finite conjugacy and model
coefficient inverses from their actual nonsingular matrices and observed data.
Source: finite determinant/adjugate formulas and mathlib's analytic scalar calculus.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods
open scoped BigOperators InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of an entrywise analytic finite observed coefficient matrix is analytic.
Use: all computed block-solve denominator domains are actual open analytic domains.
Article: main_krylov, lem:U, secant determinants.
Source: mathlib's finite Leibniz determinant formula.
Proof: the actual determinant is a finite sum of products of analytic entries. -/
theorem analytic_matrix_det (C : X → Matrix ι ι ℝ) (x : X)
    (hC : ∀ i j, AnalyticAt ℝ (fun p => C p i j) x) : AnalyticAt ℝ (fun p => (C p).det) x := by
  simp only [Matrix.det_apply']
  convert! Finset.analyticAt_sum (Finset.univ : Finset (Equiv.Perm ι)) (fun σ _ =>
      (analyticAt_const : AnalyticAt ℝ (fun _ : X => (Equiv.Perm.sign σ : ℝ)) x).mul
        (Finset.analyticAt_prod (Finset.univ : Finset ι) (fun i _ => hC (σ i) i))) using 1
  funext p
  simp only [Finset.sum_apply,Finset.prod_apply,Pi.mul_apply]

/-- Every entry of the actual nonsingular inverse of an analytic observed coefficient matrix is analytic.
Use: the implemented inverses are locally regular at their proved true quadratic domains.
Article: main_krylov, lem:U, actual model and conjugacy solves.
Source: mathlib's adjugate determinant formula and analytic reciprocal away from zero.
Proof: the inverse is the adjugate times the reciprocal of its nonzero
determinant; each adjugate entry is a determinant with one constant row. -/
theorem analytic_matrix_inv (C : X → Matrix ι ι ℝ) (x : X)
    (hC : ∀ i j, AnalyticAt ℝ (fun p => C p i j) x) (hx : (C x).det≠0) (i j : ι) :
    AnalyticAt ℝ (fun p => (C p)⁻¹ i j) x := by
  -- This proves regularity of the totalized inverse precisely on its genuine solve domain.
  have ha : AnalyticAt ℝ (fun p => (C p).adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    apply analytic_matrix_det
    intro a b
    by_cases h : a=j
    · subst a
      simpa only [Matrix.updateRow_apply,ite_true] using
        (analyticAt_const : AnalyticAt ℝ (fun _ : X => (Pi.single i (1 : ℝ) : ι → ℝ) b) x)
    · simpa only [Matrix.updateRow_apply,h,ite_false] using hC a b
  convert! ((analytic_matrix_det C x hC).inv hx).mul ha using 1
  funext p
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul,Pi.mul_apply,Pi.inv_apply]

/-- Every actual finite model coefficient is analytic in the analytic stored vectors, residual and model entries near a genuine model inverse.
Use: establishes the source's smooth coefficient condition for actual RFC/XRFC block solves.
Article: main_krylov, def:classes, smooth model correction coefficients.
Proof: each computed coefficient is a finite sum of analytic inverse entries
times actual analytic residual pairings, with the implemented minus sign. -/
theorem analytic_modelCoefficients (s : X → ι → E) (C : X → Matrix ι ι ℝ) (g : X → E) (x : X)
    (hs : ∀ i, AnalyticAt ℝ (fun p => s p i) x)
    (hC : ∀ i j, AnalyticAt ℝ (fun p => C p i j) x) (hg : AnalyticAt ℝ g x)
    (hx : (C x).det≠0) (i : ι) : AnalyticAt ℝ (fun p => modelCoefficients (s p) (C p) (g p) i) x := by
  change AnalyticAt ℝ (fun p => -(∑ j, (C p)⁻¹ i j*inner ℝ (s p j) (g p))) x
  convert! (Finset.analyticAt_sum Finset.univ (fun j _ => (analytic_matrix_inv C x hC hx i j).mul
      (analytic_inner (hs j) hg))).neg using 1
  funext p
  simp only [Finset.sum_apply,Pi.mul_apply,Pi.neg_apply]

/-- Every actual finite FC conjugacy coefficient is analytic in the observed vectors and residual at its genuine quadratic inverse domain.
Use: actual direction coefficients satisfy the source's smoothness condition without assuming regularity of an inverse solve.
Article: main_krylov, def:classes and lem:U, β=(YᵀS)⁻¹Yᵀg.
Proof: actual observed cross Gram entries are analytic inner products and each
implemented coefficient is the corresponding finite inverse-entry sum. -/
theorem analytic_conjugacyCoefficients (s y : X → ι → E) (g : X → E) (x : X)
    (hs : ∀ i, AnalyticAt ℝ (fun p => s p i) x) (hy : ∀ i, AnalyticAt ℝ (fun p => y p i) x)
    (hg : AnalyticAt ℝ g x) (hx : (crossGram (y x) (s x)).det≠0) (i : ι) :
    AnalyticAt ℝ (fun p => conjugacyCoefficients (s p) (y p) (g p) i) x := by
  change AnalyticAt ℝ (fun p => ∑ j, (crossGram (y p) (s p))⁻¹ i j*inner ℝ (y p j) (g p)) x
  convert! Finset.analyticAt_sum Finset.univ (fun j _ =>
      (analytic_matrix_inv (fun p => crossGram (y p) (s p)) x
        (fun a b => analytic_inner (hy a) (hs b)) hx i j).mul (analytic_inner (hy j) hg)) using 1
  funext p
  simp only [Finset.sum_apply,Pi.mul_apply]

/-- The actual finite FC direction solve is analytic on its true nonsingular observed-data domain.
Use: the adaptive trajectory regularity induction uses the implemented direction, not a postulated analytic response.
Article: main_krylov, lem:U, actual block direction solve.
Proof: combine the proved actual analytic coefficients with their actual
analytic stored vectors in the implemented finite physical displacement. -/
theorem analytic_conjugacyDirection (s y : X → ι → E) (g : X → E) (x : X)
    (hs : ∀ i, AnalyticAt ℝ (fun p => s p i) x) (hy : ∀ i, AnalyticAt ℝ (fun p => y p i) x)
    (hg : AnalyticAt ℝ g x) (hx : (crossGram (y x) (s x)).det≠0) :
    AnalyticAt ℝ (fun p => conjugacyDirection (s p) (y p) (g p)) x := by
  convert! hg.neg.add (Finset.analyticAt_sum Finset.univ (fun i _ =>
      (analytic_conjugacyCoefficients s y g x hs hy hg hx i).smul (hs i))) using 1
  funext p
  simp only [conjugacyDirection,combine,Finset.sum_apply,Pi.smul_apply',Pi.add_apply,Pi.neg_apply]

end
end krylov.Stability
