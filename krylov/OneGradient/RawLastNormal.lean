import krylov.Realization.RawCG
import krylov.OneGradient.CGFibre
import krylov.OneGradient.PhysicalFibre
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), actual supplied-Jacobi last-coordinate dictionary.
Use: turn original physical last-Lanczos completions into literal last-diagonal
updates on genuine supplied irreducible tridiagonal references.
Source: actual raw-matrix CG residual units, proved full active spectral support
and the genuine last-Lanczos normal; the possible orientation sign cancels.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix chebyshev1 krylov.Reference krylov.Realization
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual first-site gradient of a genuine positive irreducible supplied
tridiagonal reference has its full original physical gradient spectral support.
Use: all physical Lanczos fibre definitions receive a derived full atom count.
Article: main_krylov, s5:fibre(b), genuine supplied-matrix information family.
Proof: reuse the actual raw first-site CG stopping count and the proved equality
of physical-gradient and canonical-error active spectral supports. -/
theorem raw_first_site_full_gradient_support
    (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin (n+1),i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin (n+1),i.val+1=j.val → T i j < 0) :
    (activeSpectralValues T hT.1 (WithLp.toLp 2 (JacobiData.site (n+1) 0))).card=n+1 :=
  (gradientSpectralData_count T hT _).trans (raw_referenceAtomCount T hT htri hneg)

/-- The actual positively oriented last Lanczos normal of a true supplied
irreducible Jacobi matrix is the real final coordinate site up to a scalar
whose square is one.
Use: the orientation is derived from actual native CG, not assumed as a frame.
Article: main_krylov, s5:fibre(b), real last-coordinate normal.
Proof: the actual normalized final active CG residual is the supplied final
unit site. Its proved last-Lanczos normal decomposition identifies the same
unit line. Both real unit norms force the scalar square to equal one. -/
theorem raw_last_lanczos_site
    (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin (n+1),i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin (n+1),i.val+1=j.val → T i j < 0)
    (hg : WithLp.toLp 2 (JacobiData.site (n+1) 0)≠0)
    (hc : (activeSpectralValues T hT.1 (WithLp.toLp 2 (JacobiData.site (n+1) 0))).card=n+1) :
    ∃ c : ℝ,c^2=1 ∧ WithLp.toLp 2 (JacobiData.site (n+1) n)=
      c • lastLanczosVector T hT (WithLp.toLp 2 (JacobiData.site (n+1) 0)) hg hc := by
  let g : EuclideanSpace ℝ (Fin (n+1)) := WithLp.toLp 2 (JacobiData.site (n+1) 0)
  let r := CG.gradient (cgOperator T) g n
  let z := lastLanczosVector T hT g hg hc
  let c := ‖r‖⁻¹*inner ℝ z r
  have hr : r=(inner ℝ z r) • z := (last_cg_gradient_normal T hT g hg hc).1
  have he : WithLp.toLp 2 (JacobiData.site (n+1) n)=c • z := by
    rw [← raw_cg_residualUnit T hT htri hneg n (Nat.lt_succ_self n)]
    change ‖r‖⁻¹ • r=c • z
    calc
      _=‖r‖⁻¹ • ((inner ℝ z r) • z) := congrArg (fun v => ‖r‖⁻¹ • v) hr
      _=c • z := by rw [smul_smul]
  have hunit : ‖WithLp.toLp 2 (JacobiData.site (n+1) n)‖=1 := by
    rw [JacobiData.site_eq_single (n+1) n (Nat.lt_succ_self n)]
    simp
  have hnorm := congrArg norm he
  rw [hunit,norm_smul,last_lanczos_unit T hT g hg hc,mul_one,Real.norm_eq_abs] at hnorm
  refine ⟨c,?_,he⟩
  nlinarith [sq_abs c]

/-- The actual last physical Lanczos rank-one form is exactly the genuine
last-site coordinate rank-one form of the supplied Jacobi matrix.
Use: a source last-pivot update becomes a literal physical diagonal update.
Article: main_krylov, s5:fibre(b), actual last-coordinate rank-one equality.
Proof: reuse the actual unit-line dictionary. Both scalar factors occur in
the outer product, so their proved square one removes the orientation sign. -/
theorem raw_last_lanczos_rankOne
    (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin (n+1),i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin (n+1),i.val+1=j.val → T i j < 0)
    (hg : WithLp.toLp 2 (JacobiData.site (n+1) 0)≠0)
    (hc : (activeSpectralValues T hT.1 (WithLp.toLp 2 (JacobiData.site (n+1) 0))).card=n+1) :
    let z := WithLp.ofLp (lastLanczosVector T hT (WithLp.toLp 2 (JacobiData.site (n+1) 0)) hg hc)
    vecMulVec z z=vecMulVec (Pi.single (Fin.last n) 1) (Pi.single (Fin.last n) 1) := by
  obtain ⟨c,hc2,he⟩ := raw_last_lanczos_site T hT htri hneg hg hc
  have hs : JacobiData.site (n+1) n=c • WithLp.ofLp
      (lastLanczosVector T hT (WithLp.toLp 2 (JacobiData.site (n+1) 0)) hg hc) := congrArg WithLp.ofLp he
  dsimp only
  have hsite : JacobiData.site (n+1) n=Pi.single (Fin.last n) 1 :=
    JacobiData.site_eq_single (n+1) n (Nat.lt_succ_self n)
  rw [← hsite,hs]
  rw [smul_vecMulVec,vecMulVec_smul,smul_smul,← pow_two,hc2,one_smul]

/-- The genuine last Jacobi pivot measured by physical Lanczos is the actual
last diagonal entry of the original supplied irreducible tridiagonal matrix.
Use: anchor physical completion parameters at their true supplied-matrix values.
Article: main_krylov, s5:fibre(b), actual measured last diagonal.
Proof: the actual final unit site and last Lanczos normal differ only by a
scalar of square one, so their real quadratic forms agree. The final unit
site quadratic form is exactly the supplied final diagonal entry. -/
theorem raw_last_lanczos_pivot
    (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin (n+1),i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin (n+1),i.val+1=j.val → T i j < 0)
    (hg : WithLp.toLp 2 (JacobiData.site (n+1) 0)≠0)
    (hc : (activeSpectralValues T hT.1 (WithLp.toLp 2 (JacobiData.site (n+1) 0))).card=n+1) :
    lastJacobiPivot T hT (WithLp.toLp 2 (JacobiData.site (n+1) 0)) hg hc=T (Fin.last n) (Fin.last n) := by
  obtain ⟨c,hc2,he⟩ := raw_last_lanczos_site T hT htri hneg hg hc
  have hpair := congrArg (fun v : EuclideanSpace ℝ (Fin (n+1)) => inner ℝ v (cgOperator T v)) he
  rw [map_smul,real_inner_smul_left,real_inner_smul_right,← mul_assoc,← pow_two,hc2,one_mul] at hpair
  rw [JacobiData.site_eq_single (n+1) n (Nat.lt_succ_self n)] at hpair
  have hsite : inner ℝ (WithLp.toLp 2 (Pi.single (Fin.last n) 1))
      (cgOperator T (WithLp.toLp 2 (Pi.single (Fin.last n) 1)))=T (Fin.last n) (Fin.last n) := by
    rw [cgOperator,Matrix.toEuclideanCLM_toLp,EuclideanSpace.inner_toLp_toLp,star_trivial]
    simp
  exact hpair.symm.trans hsite

/-- The actual physical information-fibre completion of a genuine supplied
Jacobi matrix changes precisely its original final physical diagonal.
Use: explicit irreducible sharp limiting families use the true source fibre.
Article: main_krylov, s5:fibre(b), actual supplied-matrix completion dictionary.
Proof: insert the proved actual last-coordinate rank-one and pivot identities
into the original physical Lanczos completion definition. -/
theorem raw_lanczos_completion_diagonal
    (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin (n+1),i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin (n+1),i.val+1=j.val → T i j < 0)
    (hg : WithLp.toLp 2 (JacobiData.site (n+1) 0)≠0)
    (hc : (activeSpectralValues T hT.1 (WithLp.toLp 2 (JacobiData.site (n+1) 0))).card=n+1) (b : ℝ) :
    lanczosCompletion T hT (WithLp.toLp 2 (JacobiData.site (n+1) 0)) hg hc b=
      T+(b-T (Fin.last n) (Fin.last n)) • vecMulVec (Pi.single (Fin.last n) 1) (Pi.single (Fin.last n) 1) := by
  dsimp only [lanczosCompletion]
  rw [raw_last_lanczos_pivot T hT htri hneg hg hc]
  exact congrArg (fun M => T+(b-T (Fin.last n) (Fin.last n)) • M)
    (raw_last_lanczos_rankOne T hT htri hneg hg hc)

end
end krylov.OneGradient
