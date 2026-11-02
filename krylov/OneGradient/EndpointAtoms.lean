import krylov.OneGradient.MomentAttainment
import krylov.OneGradient.PhysicalSpectralEndpoints
import krylov.OneGradient.CompletionCG
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), prescribed nodes of genuine endpoint measures.
Use: connect the actual physical endpoint eigenvectors to the positive spectral
atoms of the constructed principal representations.
Source: the real spectral theorem, full original active support and actual
zero-Schur-pivot physical endpoint eigenvectors, all with derived domains.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference
variable {m n : ℕ}

/-- A true nonzero eigenvector gives an actual spectral-basis eigenvalue.
Use: prescribed physical endpoint nodes are connected to real spectral atoms.
Article: main_krylov, s5:moment(b).
Proof: a genuine orthogonal eigenbasis preserves a nonzero vector, and one
nonzero coordinate in its diagonal eigenvalue equation fixes the actual eigenvalue. -/
theorem physical_eigenvalue_in_basis (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian)
    (t : ℝ) (v : Fin m → ℝ) (hv : v≠0) (he : A*ᵥ v=t • v) :
    ∃ i : Fin m,hA.eigenvalues i=t := by
  let B := chebyshev1.SpectralBasis.ofHermitian A hA
  let w := B.Qᵀ*ᵥ v
  have hback : B.Q*ᵥ w=v := by
    change B.Q*ᵥ (B.Qᵀ*ᵥ v)=v
    rw [Matrix.mulVec_mulVec,B.mul_transpose,Matrix.one_mulVec]
  have hw : w≠0 := by
    intro hz
    rw [hz,Matrix.mulVec_zero] at hback
    exact hv hback.symm
  have hd : Matrix.diagonal B.eigenvalues*ᵥ w=t • w := by
    rw [← B.diagonalize,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,hback,he,Matrix.mulVec_smul]
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hw
  have hwi : w i≠0 := hi
  have hc := congrFun hd i
  simp only [Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul] at hc
  exact ⟨i,mul_right_cancel₀ hwi hc⟩

/-- Every actual physical eigenvalue is a positive gradient spectral atom
when the original reference has the full ambient atom count.
Use: no prescribed endpoint node or nonzero endpoint weight is assumed.
Article: main_krylov, s5:moment(b).
Proof: the proved full-count coordinate theorem gives nonzero canonical
coordinates; the actual positive eigenvalue square root gives nonzero gradient
coordinates. The genuine active-value enumeration then supplies the actual node. -/
theorem full_gradient_eigenvalue_node (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (hg : g≠0) (hc : referenceAtomCount A hA g=m)
    (t : ℝ) (ht : ∃ v : Fin m → ℝ,v≠0 ∧ A*ᵥ v=t • v) :
    ∃ j,(gradientSpectralData A hA g hg).node j=t := by
  obtain ⟨v,hv,he⟩ := ht
  obtain ⟨i,hi⟩ := physical_eigenvalue_in_basis A hA.1 t v hv he
  have hcoord : inner ℝ (hA.1.eigenvectorBasis i) g≠0 := by
    rw [gradient_spectral_coordinate A hA g i]
    exact mul_ne_zero (Real.sqrt_pos.mpr (hA.eigenvalues_pos i)).ne'
      ((full_atoms_coordinates A hA g hc).2 i)
  have hmem : t∈activeSpectralValues A hA.1 g := by
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hcoord⟩,hi⟩
  let s : activeSpectralValues A hA.1 g := ⟨t,hmem⟩
  refine ⟨(activeSpectralValues A hA.1 g).equivFin s,?_⟩
  change (((activeSpectralValues A hA.1 g).equivFin.symm
    ((activeSpectralValues A hA.1 g).equivFin s)).val)=t
  rw [Equiv.symm_apply_apply]

/-- Both actual physical endpoint spectral probability measures have the
source-prescribed endpoint as one of their genuine strictly positive atoms.
Use: the two genuine constructed measures are actual Gauss--Radau endpoint rules.
Article: main_krylov, s5:moment(b).
Proof: original feasibility derives actual positive endpoint completions and
full support. Their true zero-Schur-pivot eigenvectors give the prescribed
actual spectral atom through the real full-support eigenbasis dictionary. -/
theorem spectral_endpoint_atoms
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (I : chebyshev1.SpectralInterval)
    (hne : ∃ b : ℝ,(lanczosCompletion A hA g hg hc b-I.mu • 1).PosSemidef ∧
      (I.L • 1-lanczosCompletion A hA g hg hc b).PosSemidef) :
    let lo := spectralLowerPivot A hA g hg hc I.mu
    let hi := spectralUpperPivot A hA g hg hc I.L
    ∃ hlo : (lanczosCompletion A hA g hg hc lo).PosDef,
      ∃ hhi : (lanczosCompletion A hA g hg hc hi).PosDef,
      (∃ j,(gradientSpectralData (lanczosCompletion A hA g hg hc lo) hlo g hg).node j=I.mu) ∧
      (∃ j,(gradientSpectralData (lanczosCompletion A hA g hg hc hi) hhi g hg).node j=I.L) := by
  let lo := spectralLowerPivot A hA g hg hc I.mu
  let hi := spectralUpperPivot A hA g hg hc I.L
  have hr := physical_spectral_fibre_interval A hA g hg hc I.mu I.L hne
  have hlband := (hr.2 lo).mpr ⟨le_rfl,hr.1⟩
  have hhband := (hr.2 hi).mpr ⟨hr.1,le_rfl⟩
  have hlo := spectral_fibre_completion_positive A hA g hg hc I.mu lo I.mu_pos hlband.1
  have hhi := spectral_fibre_completion_positive A hA g hg hc I.mu hi I.mu_pos hhband.1
  have he := physical_fibre_endpoint_eigenvectors A hA g hg hc I.mu I.L hne
  refine ⟨hlo,hhi,?_,?_⟩
  · exact full_gradient_eigenvalue_node _ hlo g hg (completion_full_atoms A hA g hg hc lo hlo) I.mu he.1
  · exact full_gradient_eigenvalue_node _ hhi g hg (completion_full_atoms A hA g hg hc hi hhi) I.L he.2

end
end krylov.OneGradient
