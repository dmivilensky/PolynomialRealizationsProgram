import krylov.OneGradient.PhysicalFibre
import krylov.Envelope.KrylovFlags
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(a).
Use: derive the actual CG last-gradient geometry, the genuine inverse-energy
step length and common prefix states on the original physical information fibre.
Source: the proved actual CG invariants, finite active-atom termination and
the derived positively oriented Lanczos hyperplane.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference
variable {n : ℕ}

/-- Full physical gradient support is exactly the original full CG atom count.
Use: derive all real nonstagnation and termination hypotheses from source data.
Article: main_krylov, s5:fibre(a).
Proof: reuse equality of the actual gradient and energy spectral supports. -/
theorem full_gradient_atom_count (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1)))
    (hc : (activeSpectralValues A hA.1 g).card=n+1) : referenceAtomCount A hA g=n+1 :=
  (gradientSpectralData_count A hA g).symm.trans hc

/-- The actual penultimate CG gradient is a nonzero multiple of the actual
positively oriented last Lanczos vector.
Use: fix the original source's gamma and last-direction curvature normalization.
Article: main_krylov, s5:fibre(a), g_(n−1)=gamma*z.
Proof: the real CG Galerkin condition annihilates the whole known hyperplane.
Subtract the normal component; its true squared norm is zero. Actual full
support then makes the normal coefficient nonzero. -/
theorem last_cg_gradient_normal
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) :
    let z := lastLanczosVector A hA g hg hc
    let r := CG.gradient (cgOperator A) g n
    r=(inner ℝ z r) • z ∧ inner ℝ z r≠0 := by
  let z := lastLanczosVector A hA g hg hc
  let r := CG.gradient (cgOperator A) g n
  let p := r-(inner ℝ z r) • z
  have hp := cgOperator_positive A hA
  have hpre (i : ℕ) (hi : i<n+1) : CG.gradient (cgOperator A) g i≠0 :=
    cg_nonstagnation A hA g i (by rw [full_gradient_atom_count A hA g hc];exact hi)
  have hzz : inner ℝ z z=1 := by rw [real_inner_self_eq_norm_sq,last_lanczos_unit A hA g hg hc,one_pow]
  have hzp : inner ℝ z p=0 := by
    simp only [p,inner_sub_right,real_inner_smul_right,hzz,mul_one,sub_self]
  have hflag : p∈CG.krylovSpace (cgOperator A) g n :=
    (krylov_last_lanczos_hyperplane A hA g hg hc p).mpr hzp
  have hpr : inner ℝ p r=0 := CG.gradient_orthogonal_krylov _ hp.1 hp.2 g n
    (fun i hi => hpre i (by omega)) hflag
  have hpz : inner ℝ p z=0 := (real_inner_comm p z).symm.trans hzp
  have hpp : inner ℝ p p=0 := by
    change inner ℝ p (r-(inner ℝ z r) • z)=0
    rw [inner_sub_right,real_inner_smul_right,hpr,hpz,mul_zero,sub_self]
  have he : r=(inner ℝ z r) • z := sub_eq_zero.mp (inner_self_eq_zero.mp hpp)
  refine ⟨he,?_⟩
  intro hz
  exact hpre n (Nat.lt_succ_self n) (by change r=0;rw [he,hz,zero_smul])

/-- The original last CG step equals the genuine inverse quadratic energy of
the last physical Lanczos normal.
Use: express the central-fibre interval in the article's measured alpha units.
Article: main_krylov, s5:fibre(a,c), zᵀA⁻¹z=alpha_(n−1).
Proof: apply the actual inverse to the genuine terminating last CG update.
Pair it with the unit Lanczos normal and use the actual negative residual-energy
search pairing; cancel only the proved nonzero last-gradient coefficient. -/
theorem last_inverse_pivot_cg_length
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) :
    lastInversePivot A hA g hg hc=CG.length (cgOperator A) g n := by
  let Q := cgOperator A
  let z := lastLanczosVector A hA g hg hc
  let r := CG.gradient Q g n
  let d := CG.direction Q g n
  let a := CG.length Q g n
  let gamma := inner ℝ z r
  have hp := cgOperator_positive A hA
  have hpre (i : ℕ) (hi : i<n+1) : CG.gradient Q g i≠0 :=
    cg_nonstagnation A hA g i (by rw [full_gradient_atom_count A hA g hc];exact hi)
  have hinv := CG.invariant Q hp.1 hp.2 g n (fun i hi => hpre i (by omega))
  obtain ⟨hgeom,hgamma⟩ := last_cg_gradient_normal A hA g hg hc
  change r=gamma • z at hgeom
  change gamma≠0 at hgamma
  have hzd : inner ℝ z d= -gamma := by
    have hs := hinv.search_pair
    change inner ℝ d r= -‖r‖^2 at hs
    rw [hgeom,real_inner_smul_right,real_inner_comm z d,norm_smul,
      last_lanczos_unit A hA g hg hc,Real.norm_eq_abs,mul_one,sq_abs] at hs
    apply (mul_left_cancel₀ hgamma)
    nlinarith
  have hterm : CG.gradient Q g (n+1)=0 := by
    simpa only [full_gradient_atom_count A hA g hc] using cg_terminates A hA g
  have hfinal : gamma • z+a • Q d=0 := by
    rw [CG.gradient_succ] at hterm
    change r+a • Q d=0 at hterm
    rwa [hgeom] at hterm
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hcancel (v : EuclideanSpace ℝ (Fin (n+1))) : cgOperator A⁻¹ (Q v)=v := by
    have hh := congrArg (fun M => cgOperator M v) (nonsing_inv_mul A hdet)
    change cgOperator A⁻¹ (cgOperator A v)=v
    simpa only [cgOperator,map_mul,mul_apply_eq_comp,map_one,one_apply_eq_self] using hh
  have hvec := congrArg (cgOperator A⁻¹) hfinal
  simp only [map_add,map_smul,hcancel,map_zero] at hvec
  have hpair := congrArg (fun v => inner ℝ z v) hvec
  simp only [inner_add_right,real_inner_smul_right,inner_zero_right,hzd] at hpair
  have he : inner ℝ z (cgOperator A⁻¹ z)=a := by
    apply mul_left_cancel₀ hgamma
    nlinarith
  change lastInversePivot A hA g hg hc=a
  simpa only [lastInversePivot,z,cgOperator,Matrix.inner_toEuclideanCLM,star_trivial] using he

/-- Every real CG state before the last curvature query depends only on the
original known operator restriction.
Use: the last physical direction and gradient are common to all completions,
rather than stipulated by a fibre record.
Article: main_krylov, s5:fibre(a).
Proof: each genuine reference direction is in the known Krylov flag; reuse
the actual single-probe CG prefix comparison theorem. -/
theorem cg_information_prefix (Q C : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
    EuclideanSpace ℝ (Fin (n+1))) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v)) (g : EuclideanSpace ℝ (Fin (n+1)))
    (hpre : ∀ k<n,CG.gradient Q g k≠0)
    (hact : ∀ v∈CG.krylovSpace Q g n,C v=Q v) (k : ℕ) (hk : k≤n) :
    cgRun C g k=cgRun Q g k := by
  have hs : ∀ j<n,Q (cgRun Q g j).direction=C (cgRun Q g j).direction := by
    intro j hj
    apply Eq.symm
    apply hact
    apply krylov.Envelope.krylovSpace_mono Q g (show j+1≤n by omega)
    apply krylov.Envelope.cgDirection_mem_krylov Q g j
    intro i hi
    exact ((CG.invariant Q hQ hpos g (j+1) (fun i hi => hpre i (by omega))).lines_pos i hi).ne'
  exact (cgRun_prefix_eq Q C g n hs k hk).symm

end
end krylov.OneGradient
