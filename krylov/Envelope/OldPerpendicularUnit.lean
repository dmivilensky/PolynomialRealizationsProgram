import krylov.LinearAlgebra.PerpendicularPlaneUnit
import krylov.Envelope.ExploredFlag
import krylov.Reference.EnergyPositive

set_option autoImplicit false
/-!
Article: main_krylov, s3:thm:cf, genuine earlier-flag perpendicular unit vector.
Use: construct the actual unit direction for the true final cross-increment
forcing witness, including the real zero-tilt two-step boundary.
Source: genuine nonstagnating CG orthonormal prefixes and the proved real
orthonormal-plane perpendicular unit construction.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.LinearAlgebra
variable {n : ℕ}

/-- Every genuine active horizon of at least two steps has a true earlier-flag unit vector orthogonal to any actual target vanishing at the real two-step boundary.
Use: Every genuine active horizon of at least two steps has a true earlier-flag unit vector orthogonal to any actual target vanishing at the real two-step boundary.
Article: main_krylov, s3:thm:cf, genuine earlier-flag perpendicular unit vector.
Proof: At two steps choose the actual first CG unit step. Otherwise the genuine first two CG unit steps form a true old plane; its real perpendicular unit construction stays inside the actual earlier explored flag. -/
theorem old_flag_perpendicular_unit (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (z : EuclideanSpace ℝ (Fin n)) (hzero : N=2 → z=0) :
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖=1 ∧ x∈exploredFlag base g (N-1) ∧ inner ℝ x z=0 := by
  -- Use the genuine active CG prefix to construct real unit old directions, with the actual two-step boundary explicit.
  have hq := canonicalCGUnitStep_orthonormal base hb g N
    (fun j hj => cg_nonstagnation base hb g j (hj.trans_le hcount))
  have hu : ‖canonicalCGUnitStep base g 0‖=1 := hq.norm_eq_one ⟨0,by omega⟩
  by_cases htwo : N=2
  · refine ⟨canonicalCGUnitStep base g 0,hu,Submodule.subset_span ⟨(⟨0,by omega⟩ : Fin (N-1)),rfl⟩,?_⟩
    rw [hzero htwo,inner_zero_right]
  · have hv : ‖canonicalCGUnitStep base g 1‖=1 := hq.norm_eq_one ⟨1,by omega⟩
    have huv : inner ℝ (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g 1)=0 := by
      have hh := (orthonormal_iff_ite.mp hq) (⟨0,by omega⟩ : Fin N) ⟨1,by omega⟩
      simpa only [Fin.mk.injEq,zero_ne_one,ite_false] using hh
    -- The genuine two-dimensional old CG plane supplies an actual unit direction orthogonal to the real target.
    obtain ⟨x,hx,hmem,horth⟩ := orthonormal_pair_perpendicular_unit
      (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g 1) z hu hv huv
    have hle : Submodule.span ℝ ({canonicalCGUnitStep base g 0,canonicalCGUnitStep base g 1} :
        Set (EuclideanSpace ℝ (Fin n)))≤exploredFlag base g (N-1) := by
      apply Submodule.span_le.mpr
      intro v hv'
      rcases Set.mem_insert_iff.mp hv' with rfl | hv'
      · exact Submodule.subset_span ⟨(⟨0,by omega⟩ : Fin (N-1)),rfl⟩
      · have he : v=canonicalCGUnitStep base g 1 := Set.mem_singleton_iff.mp hv'
        rw [he]
        exact Submodule.subset_span ⟨(⟨1,by omega⟩ : Fin (N-1)),rfl⟩
    exact ⟨x,hx,hle hmem,horth⟩
end
end krylov.Envelope
