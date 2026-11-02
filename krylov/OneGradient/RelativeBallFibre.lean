import krylov.OneGradient.CompletionCG
import krylov.LinearAlgebra.NormLineInterval
import krylov.Information.MetricSlack
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(c), original arbitrary-centre relative ball.
Use: derive the actual compact admissible pivot interval and strict physical
positivity from the real metric norm constraint on the entire information fibre.
Source: actual last-Lanczos rank-one geometry, the proved affine norm-line
interval theorem and genuine physical relative-budget/Loewner equivalence.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.LinearAlgebra krylov.Information
variable {n : ℕ}

/-- The original physical information fibre meets an arbitrary positive
centre's relative ball in an actual attained compact closed pivot interval.
Use: the source's interval endpoints exist even when the ball centre has
different Krylov information and the intersection is a singleton.
Article: main_krylov, s5:fibre(c).
Proof: normalize the genuine affine physical rank-one line. Its direction has
strictly positive norm by the actual positive inverse metric on the true unit
Lanczos normal; the proved real norm-line theorem constructs both extrema. -/
theorem relative_ball_fibre_interval
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hcenter : center.PosDef)
    (rho : ℝ) (hne : ∃ b : ℝ,relativeBudget center (lanczosCompletion A hA g hg hc b-center)≤rho) :
    ∃ lo hi : ℝ,lo≤hi ∧ ∀ b : ℝ,
      relativeBudget center (lanczosCompletion A hA g hg hc b-center)≤rho ↔ b∈Set.Icc lo hi := by
  let z := WithLp.ofLp (lastLanczosVector A hA g hg hc)
  let U := cgOperator (relativeOperator center (A-center))
  let V := cgOperator (relativeOperator center (vecMulVec z z))
  let b0 := lastJacobiPivot A hA g hg hc
  have hz : z≠0 := by
    intro hz
    have he : lastLanczosVector A hA g hg hc=0 := by ext i;exact congrFun hz i
    have hn := last_lanczos_unit A hA g hg hc
    rw [he,norm_zero] at hn
    exact zero_ne_one hn
  have hnorm : ‖V‖=z ⬝ᵥ (center⁻¹*ᵥ z) := by
    have he := rank_one_relative_budget center hcenter z 1
    simp only [one_smul,abs_one,one_mul] at he
    simpa only [V,relativeBudget,chebyshev1.opNorm,Matrix.cstar_norm_def,cgOperator] using he
  have hV : V≠0 := norm_pos_iff.mp (hnorm ▸ hcenter.inv.dotProduct_mulVec_pos hz)
  have hpath (b : ℝ) : relativeBudget center (lanczosCompletion A hA g hg hc b-center)=‖U+(b-b0) • V‖ := by
    have he : lanczosCompletion A hA g hg hc b-center=(A-center)+(b-b0) • vecMulVec z z := by
      dsimp only [lanczosCompletion,b0,z]
      abel
    rw [he]
    simp only [relativeBudget,relativeOperator,Matrix.mul_add,Matrix.add_mul,
      Matrix.mul_smul,Matrix.smul_mul,chebyshev1.opNorm,Matrix.cstar_norm_def,map_add,map_smul,U,V,cgOperator]
  obtain ⟨b,hb⟩ := hne
  obtain ⟨lo,hi,horder,hset⟩ := norm_line_interval U V hV rho ⟨b-b0,by rwa [hpath] at hb⟩
  refine ⟨b0+lo,b0+hi,add_le_add (le_refl b0) horder,?_⟩
  intro b
  rw [hpath]
  have he := Set.ext_iff.mp hset (b-b0)
  change (‖U+(b-b0) • V‖≤rho) ↔ (lo≤b-b0 ∧ b-b0≤hi) at he
  rw [he]
  change _ ↔ (b0+lo≤b ∧ b≤b0+hi)
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

/-- Every actual pivot admitted by a subunit relative ball lies strictly in
the original positive physical fibre domain.
Use: both attained ball endpoints are genuine full-atom positive references
before their actual CG error and last-step formulas are used.
Article: main_krylov, s5:fibre(c).
Proof: the true relative budget supplies a strictly positive lower multiple of
the actual centre. The independently proved physical positive-fibre criterion
then identifies the exact strict Schur half-line. -/
theorem relative_ball_fibre_positive
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hcenter : center.PosDef)
    {rho : ℝ} (hrho : 0≤rho) (hsmall : rho<1) (b : ℝ)
    (hb : relativeBudget center (lanczosCompletion A hA g hg hc b-center)≤rho) :
    lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹<b := by
  have hsym : (lanczosCompletion A hA g hg hc b).IsSymm := by
    simp only [lanczosCompletion,Matrix.IsSymm,transpose_add,transpose_smul,
      transpose_vecMulVec,hA.1.isSymm.eq]
  have hpos := (relative_displacement_base center _ hcenter hsym hrho hsmall hb).2.2
  exact (lanczos_completion_positive_iff A hA g hg hc b).mp hpos

end
end krylov.OneGradient
