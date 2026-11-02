import krylov.XR.ThresholdMoments
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.ClusterPt

/-!
Article: main_krylov, thm:metric, rigidity of coincident thresholds.
Use: even coincidence on a nonempty open set forces one positive model
eigenvalue. Source: Cauchy--Schwarz equality and density of vectors whose
coordinates in a finite orthonormal basis are all nonzero.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {p : ℕ}

/-- A genuine positive model acts diagonally in its actual orthonormal
spectral coordinates. Article: main_krylov, thm:metric. -/
theorem threshold_spectral_action (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    inner ℝ (hN.1.eigenvectorBasis i) (cgOperator N v)=
      hN.1.eigenvalues i*inner ℝ (hN.1.eigenvectorBasis i) v := by
  have he : cgOperator N (hN.1.eigenvectorBasis i)=
      hN.1.eigenvalues i • hN.1.eigenvectorBasis i := by
    ext j
    exact congrFun (hN.1.mulVec_eigenvectorBasis i) j
  have hs := (cgOperator_positive N hN).1 (hN.1.eigenvectorBasis i) v
  change inner ℝ (cgOperator N (hN.1.eigenvectorBasis i)) v=
    inner ℝ (hN.1.eigenvectorBasis i) (cgOperator N v) at hs
  rw [he,real_inner_smul_left] at hs
  exact hs.symm

/-- Every nonempty open set contains a vector with nonzero coordinates
in every genuine finite spectral direction. Article: thm:metric. -/
theorem open_exists_full_spectral_support (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (U : Set (EuclideanSpace ℝ (Fin p))) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ r∈U,∀ i,inner ℝ (hN.1.eigenvectorBasis i) r≠0 := by
  let C := hN.1.eigenvectorBasis.repr.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin p) ℝ)
  have hd : Dense (Set.pi Set.univ (fun _ : Fin p=>({0} : Set ℝ)ᶜ)) :=
    dense_pi Set.univ (fun _ _=>dense_compl_singleton 0)
  have ho : IsOpen (C '' U) := C.toHomeomorph.isOpenMap U hU
  obtain ⟨v,hv,hvU⟩ := hd.exists_mem_open ho (hne.image C)
  obtain ⟨r,hr,he⟩ := hvU
  refine ⟨r,hr,?_⟩
  intro i
  have hi := hv i (Set.mem_univ i)
  rw [←he] at hi
  change (C r) i∉({0} : Set ℝ) at hi
  change ¬(hN.1.eigenvectorBasis.repr r) i=0 at hi
  simpa only [OrthonormalBasis.repr_apply_apply] using hi

/-- A full-support residual with coinciding thresholds forces the entire
actual model to be a single positive scalar. Article: thm:metric. -/
theorem threshold_equality_full_support (N : Matrix (Fin (p+1)) (Fin (p+1)) ℝ) (hN : N.PosDef)
    (r : EuclideanSpace ℝ (Fin (p+1)))
    (hsupport : ∀ i,inner ℝ (hN.1.eigenvectorBasis i) r≠0)
    (hequal : newtonThreshold N r=zeroThreshold N r) : ∃ c : ℝ,0<c ∧ N=c • 1 := by
  let u := cgOperator N⁻¹ (cgOperator N⁻¹ r)
  have hi (v : EuclideanSpace ℝ (Fin (p+1))) : cgOperator N (cgOperator N⁻¹ v)=v := by
    simp only [cgOperator,←mul_apply_eq_comp,←map_mul,
      mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hN.det_pos.ne'),map_one,one_apply_eq_self]
  have he : cgOperator N (cgOperator N u)=r := by dsimp only [u]; rw [hi,hi]
  have hr : r≠0 := by
    intro hz
    have hh := hsupport 0
    rw [hz,inner_zero_right] at hh
    exact hh rfl
  have hu : u≠0 := by intro hz; apply hr; rw [←he,hz,map_zero,map_zero]
  have hus (i : Fin (p+1)) : inner ℝ (hN.1.eigenvectorBasis i) u≠0 := by
    intro hz
    have hh := hsupport i
    rw [←he,threshold_spectral_action N hN,threshold_spectral_action N hN,
      hz,mul_zero,mul_zero] at hh
    exact hh rfl
  have hscale := threshold_equality_square_eigenvector N hN u hu (by simpa only [he] using hequal)
  have hm (i : Fin (p+1)) :
      ‖cgOperator N (cgOperator N u)‖=‖u‖*(hN.1.eigenvalues i)^2 := by
    have hh := congrArg (fun v=>inner ℝ (hN.1.eigenvectorBasis i) v) hscale
    simp only [real_inner_smul_right,threshold_spectral_action N hN] at hh
    have hf : (‖cgOperator N (cgOperator N u)‖-‖u‖*(hN.1.eigenvalues i)^2)*
        inner ℝ (hN.1.eigenvectorBasis i) u=0 := by nlinarith only [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (hus i))
  let c := hN.1.eigenvalues 0
  have hc : 0<c := hN.eigenvalues_pos 0
  have hconstant (i : Fin (p+1)) : hN.1.eigenvalues i=c := by
    have hi := hm i
    have h₀ := hm 0
    have hnorm := norm_pos_iff.mpr hu
    have hsq : (hN.1.eigenvalues i)^2=c^2 := by dsimp only [c]; nlinarith
    exact (sq_eq_sq₀ (hN.eigenvalues_pos i).le hc.le).mp hsq
  refine ⟨c,hc,?_⟩
  apply (Matrix.toEuclideanCLM (n := Fin (p+1)) (𝕜 := ℝ)).injective
  apply ContinuousLinearMap.ext
  intro v
  apply hN.1.eigenvectorBasis.repr.injective
  ext i
  simp only [OrthonormalBasis.repr_apply_apply]
  change inner ℝ (hN.1.eigenvectorBasis i) (cgOperator N v)=
    inner ℝ (hN.1.eigenvectorBasis i) (Matrix.toEuclideanCLM (n := Fin (p+1)) (𝕜 := ℝ) (c • 1) v)
  rw [threshold_spectral_action N hN,hconstant,map_smul,map_one]
  simp only [_root_.smul_apply,one_apply_eq_self,real_inner_smul_right]

/-- Coincidence on just a nonempty open set already implies one positive
scalar model; the zero-dimensional boundary is included. Article: thm:metric. -/
theorem thresholds_open_rigidity (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (U : Set (EuclideanSpace ℝ (Fin p))) (hU : IsOpen U) (hne : U.Nonempty)
    (hequal : ∀ r∈U,r≠0 → newtonThreshold N r=zeroThreshold N r) :
    ∃ c : ℝ,0<c ∧ N=c • 1 := by
  cases p with
  | zero => exact ⟨1,zero_lt_one,Subsingleton.elim _ _⟩
  | succ n =>
    obtain ⟨r,hr,hs⟩ := open_exists_full_spectral_support N hN U hU hne
    have hne' : r≠0 := by
      intro hz
      have hh := hs 0
      rw [hz,inner_zero_right] at hh
      exact hh rfl
    exact threshold_equality_full_support N hN r hs (hequal r hr hne')

end
end krylov.XR
