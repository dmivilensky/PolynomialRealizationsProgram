import krylov.LinearAlgebra.PlanarWitness
import krylov.Envelope.FlagOrthogonality
import krylov.Reference.EnergyPositive
import krylov.Envelope.PrefixResponseCoordinates

set_option autoImplicit false
/-!
Article: main_krylov, s3:thm:cf, fresh rank-two excess witness.
Use: construct a genuine symmetric last increment with the prescribed spectral budget and old-flag image.
Source: the proved planar spectral-norm witness and orthogonality of the actual canonical CG flag.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Secant krylov.Variation krylov.LinearAlgebra Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A symmetric rank-two increment sends the final unit step to any prescribed old unit direction within its exact budget.
Use: A symmetric rank-two increment sends the final unit step to any prescribed old unit direction within its exact budget.
Article: main_krylov, s3:thm:cf, fresh rank-two excess witness.
Proof: Use the actual CG flag orthogonality and the concrete planar spectral-norm bound. -/
theorem fresh_cross_witness (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hcount : k+2≤referenceAtomCount base hb g)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖=1) (hmem : x∈exploredFlag base g (k+1))
    (w : ℝ) (hw : 0≤w) :
    let h := canonicalCGUnitStep base g (k+1)
    let D := w • planarMatrix x h 0 1 0
    D.IsSymm ∧ ‖D‖≤w ∧ cgOperator D h=w • x ∧ inner ℝ h (cgOperator D h)=0 ∧
      cgOperator D h∈exploredFlag base g (k+2) := by
  -- The newest canonical step is perpendicular to the whole preceding explored flag.
  let h := canonicalCGUnitStep base g (k+1)
  have hh : ‖h‖=1 := NormedSpace.norm_normalize (canonicalCGStep_ne_zero base hb g (k+1)
    (fun i hi => cg_nonstagnation base hb g i (by omega)))
  have horth : h∈(exploredFlag base g (k+1))ᗮ := by
    intro v hv
    have hp : h∈(oldFlag base g k)ᗮ := unitStep_prefix_oldFlag_orthogonal base hb g hcount (show k+1<k+2 by omega) (show k<k+1 by omega)
    rw [exploredFlag_eq_oldFlag base g (show 0<k+1 by omega)] at hv
    exact hp v hv
  have hxh : inner ℝ x h=0 := horth x hmem
  have hhx : inner ℝ h x=0 := by rw [real_inner_comm];exact hxh
  -- The concrete cross block has spectral norm at most one and its action has no diagonal component.
  have hunit := planar_spectral_norm_le x h hx hh hxh 0 1 (by norm_num)
  have hn : ‖planarMatrix x h 0 1 0‖≤1 := by
    simpa only [neg_zero,chebyshev1.opNorm,Matrix.cstar_norm_def] using hunit
  have ha : cgOperator (w • planarMatrix x h 0 1 0) h=w • x := by
    have hhh : inner ℝ h h=1 := by rw [real_inner_self_eq_norm_sq,hh,one_pow]
    simp only [cgOperator,map_smul,_root_.smul_apply,planarMatrix_action,hxh,hhh,
      zero_mul,one_mul,add_zero,zero_add,one_smul,zero_smul]
  refine ⟨(planarMatrix_isSymm x h 0 1 0).smul w,?_,ha,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hw]
    nlinarith
  · rw [ha,real_inner_smul_right,hhx,mul_zero]
  · rw [ha]
    exact Submodule.smul_mem _ _ (exploredFlag_mono base g (show k+1≤k+2 by omega) hmem)
end
end krylov.Envelope
