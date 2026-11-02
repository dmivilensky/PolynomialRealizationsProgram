import krylov.OneGradient.PhysicalJacobiBand
import krylov.LinearAlgebra.JacobiStrictPrefix
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), strict leading shifts and attained spectral interval.
Use: derive the true leading inverse domains from an actual feasible physical
completion, then construct the whole original closed spectral information interval.
Source: actual reconstructed irreducible Lanczos tridiagonality and the proved
positive-semidefinite Jacobi strict-prefix theorem (Meurant06, GolubMeurant10).
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.LinearAlgebra krylov.Completion
variable {n : ℕ}

/-- The original physical completion in its actual positive Jacobi coordinates.
Use: endpoint geometry always refers to the original physical operator and frame.
Article: main_krylov, s5:fibre(b). -/
def completedJacobi
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (physicalLanczosColumns A hA g hg hc)ᵀ*lanczosCompletion A hA g hg hc b*
    physicalLanczosColumns A hA g hg hc

/-- The actual completed Jacobi matrix is symmetric for every real last pivot.
Use: closed shifted spectral endpoints remain symmetric even when their shifted
whole forms become singular.
Article: main_krylov, s5:fibre(b).
Proof: the genuine physical rank-one completion is symmetric, and the actual
Lanczos coordinate congruence preserves that symmetry. -/
theorem completed_jacobi_symmetric
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ) :
    (completedJacobi A hA g hg hc b).IsSymm := by
  have hC : (lanczosCompletion A hA g hg hc b).IsSymm := by
    simp only [lanczosCompletion,Matrix.IsSymm,transpose_add,transpose_smul,
      transpose_vecMulVec,hA.1.isSymm.eq]
  simp only [completedJacobi,Matrix.IsSymm,transpose_mul,transpose_transpose,hC.eq,Matrix.mul_assoc]

/-- Actual physical pivot completions retain the original constructed Jacobi
tridiagonality, without assuming a separately chosen three-diagonal model.
Use: irreducible proper-prefix spectral margins apply to every real completion.
Article: main_krylov, s5:fibre(b).
Proof: the only changed physical compression entry is last-last, which is never
a distant off-diagonal. The actual gradient measure supplies every other zero. -/
theorem completed_jacobi_tridiagonal
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ)
    (i j : Fin (n+1)) (hfar : i.val+1 < j.val ∨ j.val+1 < i.val) :
    completedJacobi A hA g hg hc b i j=0 := by
  have hlast : ¬(i=Fin.last n ∧ j=Fin.last n) := by
    rintro ⟨rfl,rfl⟩
    simp only [Fin.val_last] at hfar
    omega
  rw [completedJacobi,physical_lanczos_completion,ite_eq_right hlast,
    physical_lanczos_jacobi,(gradientSpectralData A hA g hg).reconstructed_matrix]
  exact (gradientSpectralData A hA g hg).multiplication_tridiagonal _ _ hfar

/-- Actual physical pivot completions retain every strictly positive lower
Jacobi coupling of the original constructed Lanczos frame.
Use: the true irreducible edge domains survive both singular whole endpoint shifts.
Article: main_krylov, s5:fibre(b).
Proof: the actual physical compression changes no adjacent entry. Its original
positive upper coupling and genuine real symmetry give the lower coupling. -/
theorem completed_jacobi_edge_positive
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ)
    (i j : Fin (n+1)) (hij : i.val+1=j.val) :
    0 < completedJacobi A hA g hg hc b j i := by
  have hlast : ¬(i=Fin.last n ∧ j=Fin.last n) := by
    rintro ⟨rfl,rfl⟩
    simp only [Fin.val_last] at hij
    omega
  have hs := congrFun (congrFun (completed_jacobi_symmetric A hA g hg hc b).eq i) j
  change completedJacobi A hA g hg hc b j i=completedJacobi A hA g hg hc b i j at hs
  rw [hs,completedJacobi,physical_lanczos_completion,ite_eq_right hlast,physical_lanczos_compression]
  exact lanczosVector_adjacent_pos A hA g hg _ _ hij

/-- Every actually feasible spectral completion makes both original leading
Jacobi shifts strictly positive.
Use: the ordinary inverses in both source Gauss--Radau endpoints have proved
physical domains, even when the whole admissible interval collapses.
Article: main_krylov, s5:fibre(b), spec(J0) is strictly inside (mu,L).
Proof: true orthogonal compression gives both whole nonnegative shifts; actual
irreducible tridiagonal edges survive each shift. The proved Jacobi strict-prefix
theorem makes their proper leading blocks genuinely positive definite. -/
theorem physical_fibre_leading_strict
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (mu upper b : ℝ)
    (hlo : (lanczosCompletion A hA g hg hc b-mu • 1).PosSemidef)
    (hhi : (upper • 1-lanczosCompletion A hA g hg hc b).PosSemidef) :
    (lastLeading (physicalJacobi A hA g hg hc)-mu • 1).PosDef ∧
      (upper • 1-lastLeading (physicalJacobi A hA g hg hc)).PosDef := by
  let P := completedJacobi A hA g hg hc b
  let Z := physicalLanczosColumns A hA g hg hc
  have hZ : Zᵀ*Z=1 := physical_lanczos_orthogonal A hA g hg hc
  have hpL : (P-mu • 1).PosSemidef := by
    change (Zᵀ*lanczosCompletion A hA g hg hc b*Z-mu • 1).PosSemidef
    have he := hlo.conjTranspose_mul_mul_same Z
    simpa only [conjTranspose_eq_transpose_of_trivial,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hZ] using he
  have hpH : (upper • 1-P).PosSemidef := by
    change (upper • 1-Zᵀ*lanczosCompletion A hA g hg hc b*Z).PosSemidef
    have he := hhi.conjTranspose_mul_mul_same Z
    simpa only [conjTranspose_eq_transpose_of_trivial,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hZ] using he
  have htri (c : ℝ) (i j : Fin (n+1)) (hfar : i.val+1 < j.val ∨ j.val+1 < i.val) :
      (P-c • 1) i j=0 ∧ (c • 1-P) i j=0 := by
    have hij : i≠j := by intro he;subst j;omega
    have ht : P i j=0 := completed_jacobi_tridiagonal A hA g hg hc b i j hfar
    simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_ne hij,smul_eq_mul,mul_zero,ht,sub_self,and_self]
  have hedge (c : ℝ) (i j : Fin (n+1)) (hij : i.val+1=j.val) :
      (P-c • 1) j i≠0 ∧ (c • 1-P) j i≠0 := by
    have hne : j≠i := by intro he;subst j;omega
    have hp : 0 < P j i := completed_jacobi_edge_positive A hA g hg hc b i j hij
    simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_ne hne,smul_eq_mul,mul_zero,sub_zero,zero_sub]
    exact ⟨hp.ne',neg_ne_zero.mpr hp.ne'⟩
  have hL := jacobi_strict_prefix (P-mu • 1) hpL (fun i j hij => (htri mu i j hij).1)
    (fun i j hij => (hedge mu i j hij).1)
  have hH := jacobi_strict_prefix (upper • 1-P) hpH (fun i j hij => (htri upper i j hij).2)
    (fun i j hij => (hedge upper i j hij).2)
  have hprefix : P.submatrix Fin.castSucc Fin.castSucc=lastLeading (physicalJacobi A hA g hg hc) := by
    ext i j
    change completedJacobi A hA g hg hc b (Fin.castSucc i) (Fin.castSucc j)=_
    rw [completedJacobi,physical_lanczos_completion]
    simp only [Fin.castSucc_ne_last i,false_and,ite_false]
    rfl
  have heL : (P-mu • 1).submatrix Fin.castSucc Fin.castSucc=lastLeading (physicalJacobi A hA g hg hc)-mu • 1 := by
    simp only [Matrix.submatrix_sub,Matrix.submatrix_smul,Pi.sub_apply,Pi.smul_apply,
      Matrix.submatrix_one _ (Fin.castSucc_injective n),hprefix]
  have heH : (upper • 1-P).submatrix Fin.castSucc Fin.castSucc=upper • 1-lastLeading (physicalJacobi A hA g hg hc) := by
    simp only [Matrix.submatrix_sub,Matrix.submatrix_smul,Pi.sub_apply,Pi.smul_apply,
      Matrix.submatrix_one _ (Fin.castSucc_injective n),hprefix]
  exact ⟨heL ▸ hL,heH ▸ hH⟩

/-- A nonempty original physical spectral fibre is exactly the attained closed
Gauss--Radau Schur interval, with both ordinary inverse domains derived from
an actual feasible completion.
Use: no strict leading margin, abstract endpoint matrix or completion existence
is supplied as a structure field in the source interval theorem.
Article: main_krylov, s5:fibre(b), b_minus and b_plus.
Proof: a genuine feasible completion gives the strict leading shifts, then the
proved real physical spectral Schur equivalence covers every possible pivot.
The same witness proves the interval order, so both endpoints are admitted. -/
theorem physical_spectral_fibre_interval
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (mu upper : ℝ)
    (hne : ∃ b : ℝ,(lanczosCompletion A hA g hg hc b-mu • 1).PosSemidef ∧
      (upper • 1-lanczosCompletion A hA g hg hc b).PosSemidef) :
    let J := physicalJacobi A hA g hg hc
    let H := lastLeading J
    let x := lastCross J
    let lo := mu+x ⬝ᵥ ((H-mu • 1)⁻¹*ᵥ x)
    let hi := upper-x ⬝ᵥ ((upper • 1-H)⁻¹*ᵥ x)
    lo≤hi ∧ ∀ b : ℝ,
      ((lanczosCompletion A hA g hg hc b-mu • 1).PosSemidef ∧
        (upper • 1-lanczosCompletion A hA g hg hc b).PosSemidef) ↔ b∈Set.Icc lo hi := by
  obtain ⟨b,hblo,hbhi⟩ := hne
  obtain ⟨hlo,hhi⟩ := physical_fibre_leading_strict A hA g hg hc mu upper b hblo hbhi
  have he := physical_fibre_spectral_iff A hA g hg hc mu upper hlo hhi
  have hw := (he b).mp ⟨hblo,hbhi⟩
  exact ⟨hw.1.trans hw.2,he⟩

end
end krylov.OneGradient
