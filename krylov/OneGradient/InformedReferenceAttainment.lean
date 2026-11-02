import krylov.OneGradient.InformedAttainment
import krylov.Correction.ReferenceOperator
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), genuine CG informed coefficient attainment.
Use: attain the full original source coefficient on its actual CG frame
with the exact last-axis rank-one prior used by the physical base family.
Source: true full CG orthonormality, real old-flag geometry and the
strengthened original correlated planar/symmetric-ball attainer.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant krylov.Correction krylov.Envelope krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The full source informed constant is attained on every genuine full
CG reference of dimension at least two, with each true individual budget
and an exact canonical last-axis rank-one prior. All zero budget profiles
use the same construction, without a limiting maximizer assumption.
Use: the prior is exactly the one realized by the actual physical
last-Lanczos base family, so these source witnesses lift to real scenarios.
Article: main_krylov, thm:local(b), actual reference coefficient sharpness.
Proof: choose the actual first and last unit CG steps, which are genuinely
orthonormal. The first belongs to every true old flag; the last is in
every relevant complementary flag. Apply the existing exact rank-one
correlated attainer and identify its expression with the original source
fresh defect and staircase, retaining the same actual matrices. -/
theorem informed_reference_second_order_attained
    (base : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+2))) (hc : referenceAtomCount base hb g=n+2)
    (omega : ℕ → ℝ) (homega : ∀ l∈range (n+1),0≤omega l)
    (w c : ℝ) (hw : 0≤w) (hc0 : 0≤c) :
    ∃ E : ℕ → Matrix (Fin (n+2)) (Fin (n+2)) ℝ, ∃ R F : Matrix (Fin (n+2)) (Fin (n+2)) ℝ,
      (∀ l∈range (n+1),(E l).IsSymm ∧ ‖E l‖≤omega l) ∧ R.IsSymm ∧ ‖R‖≤c ∧
      cgOperator R=c • InnerProductSpace.rankOne ℝ
        (canonicalCGUnitStep base g (n+1)) (canonicalCGUnitStep base g (n+1)) ∧
      F.IsSymm ∧ ‖F‖≤w ∧
      let h := canonicalCGUnitStep base g (n+1)
      let f := freshDefect base g E (n+2)
      let q := inner ℝ h (cgOperator (R+∑ l∈range (n+1),E l) h)
      ‖staircaseOperator base g E F (n+2) f+q • cgOperator F h‖=
        informedConstant (∑ l∈range (n+1),omega l) w c := by
  let e := canonicalCGUnitStep base g 0
  let h := canonicalCGUnitStep base g (n+1)
  have ho := canonicalCG_frame_of_full_atoms base hb g hc
  have he : ‖e‖=1 := ho.norm_eq_one 0
  have hh : ‖h‖=1 := ho.norm_eq_one (Fin.last (n+1))
  have heh : inner ℝ e h=0 := ho.inner_eq_zero (i := 0) (j := Fin.last (n+1)) (by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [Fin.val_zero,Fin.val_last] at hv
    omega)
  obtain ⟨E,R,F,hE,hR,hRn,hRform,hF,hFn,hvalue⟩ := informed_compression_attained_rank_one
    (range (n+1)) (oldFlag base g) e h he hh heh
    (fun l _ => unitStep_mem_oldFlag base g (Nat.zero_le l))
    (fun l hl => unitStep_prefix_oldFlag_orthogonal base hb g hc.ge (by omega) (mem_range.mp hl))
    omega homega w c hw hc0
  refine ⟨E,R,F,hE,hR,hRn,hRform,hF,hFn,?_⟩
  let f := freshDefect base g E (n+2)
  let q := inner ℝ h (cgOperator R h)+∑ l∈range (n+1),inner ℝ h (cgOperator (E l) h)
  change ‖(∑ l∈range (n+1),(oldFlag base g l).starProjection
    (cgOperator (E l) ((oldFlag base g l).starProjection f)))+cgOperator F (f+q • h)‖=_ at hvalue
  have hq : inner ℝ h (cgOperator (R+∑ l∈range (n+1),E l) h)=q := by
    simp only [q,cgOperator,map_add,map_sum,_root_.add_apply,_root_.sum_apply,inner_add_right,inner_sum]
  change ‖staircaseOperator base g E F (n+2) f+_ • cgOperator F h‖=_
  rw [hq,staircaseOperator_apply]
  simpa only [show n+2-1=n+1 by omega,map_add,map_smul,add_assoc] using hvalue

end
end krylov.OneGradient
