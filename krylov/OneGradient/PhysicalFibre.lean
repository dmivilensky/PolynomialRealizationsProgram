import krylov.OneGradient.LanczosFibre
import krylov.OneGradient.RankOnePivot
set_option autoImplicit false
/-!
Article: main_krylov, s5:info and s5:fibre(a,c).
Use: construct the original physical last-Jacobi-pivot family and identify the
entire positive information fibre and the exact central relative-ball interval.
Source: the derived actual Lanczos information hyperplane, genuine physical
rank-one positivity criterion and exact metric rank-one norm.
-/

/-!
Article: krylov, Lemma C.6 [s5:fibre].

All positive completions, common physical CG states and the reciprocal last pivot are
identified; spectral and relative-ball endpoint intervals have their true physical endpoint
attainments.
Dimension n in the paper is Fin(k+1) or Fin(k+2) in wrappers. Full active spectrum supplies
nonzero last direction and strict leading spectral pencils. Relative balls use 0≤ρ<1.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant
variable {n : ℕ}

/-- The actual physical last diagonal entry in the constructed Lanczos coordinates.
Use: anchor the free parameter at the original reference's genuine Jacobi diagonal.
Article: main_krylov, s5:fibre(a).
Proof: pair the original matrix with the actual unit last Lanczos vector. -/
def lastJacobiPivot (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) : ℝ :=
  inner ℝ (lastLanczosVector A hA g hg hc) (cgOperator A (lastLanczosVector A hA g hg hc))

/-- The original physical completion with free last Jacobi diagonal b.
Use: the new matrix changes only the genuine last-Lanczos rank-one direction.
Article: main_krylov, s5:info and s5:fibre(a).
Proof: add exactly the requested last-diagonal change to the original matrix. -/
def lanczosCompletion (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  let z := WithLp.ofLp (lastLanczosVector A hA g hg hc)
  A+(b-lastJacobiPivot A hA g hg hc) • vecMulVec z z

/-- The actual inverse energy of the last Lanczos normal.
Use: determine both the strict positive half-line and the exact relative-ball radius.
Article: main_krylov, s5:fibre(a,c).
Proof: evaluate the original inverse metric quadratic form at the genuine normal. -/
def lastInversePivot (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) : ℝ :=
  let z := WithLp.ofLp (lastLanczosVector A hA g hg hc)
  z ⬝ᵥ (A⁻¹*ᵥ z)

/-- The actual physical last-normal inverse energy is strictly positive.
Use: justify the interval and reciprocal step formulas on their real domains.
Article: main_krylov, s5:fibre(a,c).
Proof: the last Lanczos vector is unit and the true inverse metric is positive. -/
theorem last_inverse_pivot_positive
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) : 0<lastInversePivot A hA g hg hc := by
  have hz : WithLp.ofLp (lastLanczosVector A hA g hg hc)≠0 := by
    intro h0
    have he : lastLanczosVector A hA g hg hc=0 := by ext i;exact congrFun h0 i
    have hn := last_lanczos_unit A hA g hg hc
    rw [he,norm_zero] at hn
    exact zero_ne_one hn
  simpa only [lastInversePivot,star_trivial] using hA.inv.dotProduct_mulVec_pos hz

/-- The physical completion has exactly its genuine last-normal rank-one operator action.
Use: transfer the already proved whole-operator information fibre to actual matrices.
Article: main_krylov, s5:fibre(a).
Proof: the matrix/operator algebra map preserves the physical rank-one update. -/
theorem lanczos_completion_operator
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ) :
    cgOperator (lanczosCompletion A hA g hg hc b)=cgOperator A+
      (b-lastJacobiPivot A hA g hg hc) • InnerProductSpace.rankOne ℝ
        (lastLanczosVector A hA g hg hc) (lastLanczosVector A hA g hg hc) := by
  simp only [lanczosCompletion,cgOperator,map_add,map_smul,
    krylov.LinearAlgebra.toEuclideanCLM_rankOne,WithLp.toLp_ofLp]

/-- Every physical completion preserves exactly the original known operator restriction.
Use: prove nonanticipating indistinguishability for the entire constructed fibre.
Article: main_krylov, s5:info and s5:fibre(a).
Proof: its actual rank-one normal annihilates the proved old Krylov hyperplane. -/
theorem lanczos_completion_information
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ)
    (v : EuclideanSpace ℝ (Fin (n+1))) (hv : v∈CG.krylovSpace (cgOperator A) g n) :
    cgOperator (lanczosCompletion A hA g hg hc b) v=cgOperator A v := by
  rw [lanczos_completion_operator]
  have hz := (krylov_last_lanczos_hyperplane A hA g hg hc v).mp hv
  simp only [_root_.add_apply,_root_.smul_apply,InnerProductSpace.rankOne_apply,
    hz,zero_smul,smul_zero,add_zero]

/-- The entire actual completion is positive exactly on its true inverse-pivot half-line.
Use: no positive-completion domain is assumed as part of a fibre structure.
Article: main_krylov, s5:fibre(a).
Proof: apply the proved physical rank-one criterion and clear the strictly
positive actual inverse energy. -/
theorem lanczos_completion_positive_iff
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ) :
    (lanczosCompletion A hA g hg hc b).PosDef ↔
      lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹<b := by
  have hh := last_inverse_pivot_positive A hA g hg hc
  have hz : WithLp.ofLp (lastLanczosVector A hA g hg hc)≠0 := by
    intro h0
    have he : lastInversePivot A hA g hg hc=0 := by simp only [lastInversePivot,h0,zero_dotProduct]
    linarith
  rw [lanczosCompletion,rank_one_positive_iff A hA _ hz]
  change 0<1+(b-lastJacobiPivot A hA g hg hc)*lastInversePivot A hA g hg hc ↔ _
  have hi := mul_inv_cancel₀ hh.ne'
  constructor <;> intro h <;> nlinarith

/-- The relative ball on the reference's own fibre has exactly the article's
two closed last-diagonal endpoints, including zero radius.
Use: the interval is computed from the actual physical norm of every completion.
Article: main_krylov, s5:fibre(c).
Proof: the exact relative rank-one norm reduces membership to the scalar interval. -/
theorem lanczos_completion_central_ball
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho b : ℝ) :
    relativeBudget A (lanczosCompletion A hA g hg hc b-A)≤rho ↔
      lastJacobiPivot A hA g hg hc-rho/lastInversePivot A hA g hg hc≤b ∧
        b≤lastJacobiPivot A hA g hg hc+rho/lastInversePivot A hA g hg hc := by
  rw [lanczosCompletion,add_sub_cancel_left,rank_one_relative_budget A hA]
  change |b-lastJacobiPivot A hA g hg hc| *lastInversePivot A hA g hg hc≤rho ↔ _
  rw [← le_div_iff₀ (last_inverse_pivot_positive A hA g hg hc),abs_le]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

end
end krylov.OneGradient
