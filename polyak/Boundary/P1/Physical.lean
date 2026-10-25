import polyak.Boundary.P1.Finite
import polyak.Boundary.P1.ContactUnique

/-!
Article: Proposition p1physical, source roots give actual infinite feasible and optimal spectra.
Use: the finite box checker supplies scalar inequalities only; all lag and dual conclusions
are proved from the independently specified regularized source equations.
-/
noncomputable section
namespace polyak.Boundary.P1
open Spectral

/-- A checked root of the source equations gives feasibility for every lag and either sign of t. -/
theorem regularRoot_feasible {z t : ℝ} {Z : Coordinates} (hz : 0<z) (hz1 : z≤3/4)
    (hZ : regularSystem (z,Z)=0) (h : PhysicalBounds z Z) (ht : Real.cosh t=1/z) :
    FeasibleU (branchU z (Z 0)) t (spectrum (physicalAtom hz hz1 h))
      (chargeNumerator z (branchU z (Z 0)) (branchAtom z (Z 1))/Real.sinh t) := by
  exact feasibleU (physicalAtom hz hz1 h) hz hz1 ⟨h.atom_lower,h.atom_nonpos⟩
    h.u_nonneg h.u_le_one h.gap_lower (regularSystem_contacts hZ).1 ht

/-- Source root optimality has no numerical, finite-prefix, or guessed-branch premise. -/
theorem regularRoot_optimal {z t : ℝ} {Z : Coordinates} (hz : 0<z) (hz1 : z≤3/4)
    (hZ : regularSystem (z,Z)=0) (h : PhysicalBounds z Z) (ht : Real.cosh t=1/z) :
    V t=Real.arsinh (branchU z (Z 0)) := by
  exact optimal (physicalAtom hz hz1 h) hz hz1 ⟨h.atom_lower,h.atom_nonpos⟩
    h.u_nonneg h.u_le_one h.gap_lower (regularSystem_contacts hZ).1
    (regularSystem_contacts hZ).2 h.residual ht

/-- All physical roots at a fixed positive parameter coincide, by actual spectral optimality.
This analytic uniqueness also glues overlapping certified continuation boxes. -/
theorem regularRoot_unique {z : ℝ} {Z W : Coordinates} (hz : 0<z) (hz1 : z≤3/4)
    (hZ : regularSystem (z,Z)=0) (hW : regularSystem (z,W)=0)
    (hZb : PhysicalBounds z Z) (hWb : PhysicalBounds z W) : Z=W := by
  have hG : 1≤1/z := by rw [le_div_iff₀ hz]; linarith
  let t := Real.arcosh (1/z)
  have ht : Real.cosh t=1/z := Real.cosh_arcosh hG
  have hu : branchU z (Z 0)=branchU z (W 0) :=
    Real.arsinh_injective ((regularRoot_optimal hz hz1 hZ hZb ht).symm.trans
      (regularRoot_optimal hz hz1 hW hWb ht))
  exact regularRoot_unique_of_u hz hz1 hZ hW hZb hWb hu

end polyak.Boundary.P1
