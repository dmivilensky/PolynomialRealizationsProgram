import krylov.Reference.LanczosMeasure
import krylov.LinearAlgebra.CompletionWidth
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(a) and s5:info.
Use: identify the original physical Krylov information hyperplane and prove
that its entire symmetric operator fibre has just one free Jacobi coefficient.
Source: actual Lanczos polynomials and the previously proved symmetric
hyperplane annihilator; the physical hyperplane equality is derived here.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Polynomial krylov.Reference
open scoped InnerProductSpace
variable {n : ℕ}

/-- The last positively oriented Lanczos vector of the actual full-atom reference.
Use: the information fibre uses the original physical vector, not a chosen normal.
Article: main_krylov, s5:fibre(a).
Proof: select the actual last site of the constructed gradient spectral measure. -/
def lastLanczosVector (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) : EuclideanSpace ℝ (Fin (n+1)) :=
  lanczosVector A hA g hg ⟨n,by rw [hc];omega⟩

/-- The actual last Lanczos normal has norm one.
Use: fix the scalar normalization of the free physical rank-one perturbation.
Article: main_krylov, s5:fibre(a).
Proof: read the norm from the proved actual Lanczos orthonormal family. -/
theorem last_lanczos_unit (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) :
    ‖lastLanczosVector A hA g hg hc‖=1 :=
  (lanczosVector_orthonormal A hA g hg).norm_eq_one _

/-- Every actual earlier Lanczos vector belongs to the original old Krylov flag.
Use: construct the information hyperplane directly from genuine polynomial data.
Article: main_krylov, s5:fibre(a).
Proof: the actual polynomial has the indexed degree and positive leading
coefficient, so its physical action lies in the true polynomial Krylov flag. -/
theorem lanczos_vector_in_flag (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (i : Fin (activeSpectralValues A hA.1 g).card) (hi : i.val<n) :
    lanczosVector A hA g hg i∈CG.krylovSpace (cgOperator A) g n := by
  apply Submodule.smul_mem
  refine ⟨(gradientSpectralData A hA g hg).orthogonalPolynomial i,?_,rfl⟩
  apply Polynomial.mem_degreeLT.mpr
  have hd := (gradientSpectralData A hA g hg).orthogonalPolynomial_degree i
  rw [Polynomial.degree_eq_natDegree (Polynomial.leadingCoeff_ne_zero.mp hd.2.ne'),hd.1]
  exact_mod_cast hi

/-- The known Krylov space is exactly the orthogonal hyperplane of the actual
last positively oriented Lanczos vector.
Use: establish the physical information fibre without assuming its codimension
or introducing an independently supplied Lanczos representation.
Article: main_krylov, s5:fibre(a), K_(n−1)=z-perp.
Proof: lower-degree polynomial orthogonality proves one inclusion. For the
reverse, the genuine full orthonormal Lanczos family spans the physical space;
subtract its last normal component and test every generator against the old flag. -/
theorem krylov_last_lanczos_hyperplane
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (v : EuclideanSpace ℝ (Fin (n+1))) :
    v∈CG.krylovSpace (cgOperator A) g n ↔ inner ℝ (lastLanczosVector A hA g hg hc) v=0 := by
  let z := lastLanczosVector A hA g hg hc
  let M := gradientSpectralData A hA g hg
  let j : Fin (activeSpectralValues A hA.1 g).card := ⟨n,by rw [hc];omega⟩
  have ho := lanczosVector_orthonormal A hA g hg
  constructor
  · rintro ⟨p,hp,rfl⟩
    change inner ℝ (‖g‖⁻¹ • CG.polynomialAction (cgOperator A) g (M.orthogonalPolynomial j))
      (CG.polynomialAction (cgOperator A) g p)=0
    by_cases hp0 : p=0
    · rw [hp0,map_zero,inner_zero_right]
    have hdeg : p.natDegree<n := by
      have h := Polynomial.mem_degreeLT.mp hp
      rw [Polynomial.degree_eq_natDegree hp0] at h
      exact_mod_cast h
    rw [real_inner_smul_left,gradientSpectralData_inner A hA g hg,
      M.evaluate_orthogonalPolynomial,M.polynomialBasis_orthogonal_lower hdeg,mul_zero,mul_zero]
  · intro hv
    change inner ℝ z v=0 at hv
    let P : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
      ContinuousLinearMap.id ℝ _-InnerProductSpace.rankOne ℝ z z
    have hspan : Submodule.span ℝ (Set.range (lanczosVector A hA g hg))=⊤ :=
      ho.linearIndependent.span_eq_top_of_card_eq_finrank' (by simpa using hc)
    have hle : Submodule.span ℝ (Set.range (lanczosVector A hA g hg))≤
        (CG.krylovSpace (cgOperator A) g n).comap P.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change lanczosVector A hA g hg i-inner ℝ z (lanczosVector A hA g hg i) • z∈CG.krylovSpace (cgOperator A) g n
      by_cases hij : i=j
      · subst i
        have hzz : inner ℝ z z=1 := by
          rw [real_inner_self_eq_norm_sq,last_lanczos_unit A hA g hg hc,one_pow]
        change z-inner ℝ z z • z∈CG.krylovSpace (cgOperator A) g n
        rw [hzz,one_smul,sub_self]
        exact Submodule.zero_mem _
      · have hz : inner ℝ z (lanczosVector A hA g hg i)=0 := ho.inner_eq_zero (Ne.symm hij)
        rw [hz,zero_smul,sub_zero]
        apply lanczos_vector_in_flag A hA g hg i
        have hi : i.val<n+1 := i.isLt.trans_eq hc
        have hne : i.val≠n := by intro he;exact hij (Fin.ext he)
        omega
    have hp := hle (show v∈Submodule.span ℝ (Set.range (lanczosVector A hA g hg)) by rw [hspan];trivial)
    change v-inner ℝ z v • z∈CG.krylovSpace (cgOperator A) g n at hp
    simpa only [hv,zero_smul,sub_zero] using hp

/-- All symmetric physical operators with the same original Krylov information
are exactly the one-parameter last-Lanczos rank-one family.
Use: derive the entire physical information fibre, not only some indistinguishable twins.
Article: main_krylov, s5:fibre(a).
Proof: the actual old flag is the proved Lanczos hyperplane; apply the reused
symmetric annihilator to the difference and identify its actual rank-one action. -/
theorem krylov_information_rank_one
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (C : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (hC : C.toLinearMap.IsSymmetric) :
    (∀ v∈CG.krylovSpace (cgOperator A) g n,C v=cgOperator A v) ↔
      ∃ t : ℝ,C=cgOperator A+t • InnerProductSpace.rankOne ℝ
        (lastLanczosVector A hA g hg hc) (lastLanczosVector A hA g hg hc) := by
  let z := lastLanczosVector A hA g hg hc
  constructor
  · intro hact
    have hs := hC.sub (cgOperator_positive A hA).1
    have hz (u : EuclideanSpace ℝ (Fin (n+1))) (hu : inner ℝ z u=0) : (C-cgOperator A) u=0 := by
      exact sub_eq_zero.mpr (hact u ((krylov_last_lanczos_hyperplane A hA g hg hc u).mpr hu))
    have he := krylov.LinearAlgebra.symmetric_hyperplane_annihilator (C-cgOperator A) hs z
      (last_lanczos_unit A hA g hg hc) hz
    refine ⟨inner ℝ z ((C-cgOperator A) z),?_⟩
    apply ContinuousLinearMap.ext
    intro u
    have hh := he u
    change C u-cgOperator A u=(inner ℝ z u*inner ℝ z ((C-cgOperator A) z)) • z at hh
    change C u=cgOperator A u+inner ℝ z ((C-cgOperator A) z) • (inner ℝ z u • z)
    rw [smul_smul,mul_comm]
    simpa only [add_comm] using (sub_eq_iff_eq_add).mp hh
  · rintro ⟨t,rfl⟩ v hv
    have hz := (krylov_last_lanczos_hyperplane A hA g hg hc v).mp hv
    simp only [_root_.add_apply,_root_.smul_apply,
      InnerProductSpace.rankOne_apply,hz,zero_smul,smul_zero,add_zero]

end
end krylov.OneGradient
