import krylov.Methods.PairBasisChange
import krylov.LinearAlgebra.InverseComparison
import krylov.Correction.PairingOrders
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine observed solve comparisons.
Use: transfer actual finite model and gradient errors through the real
physical synthesis, retaining the spectral norm on all matrix errors.
Source: finite sums, real Cauchy--Schwarz and genuine inverse continuity.
-/

namespace krylov.Methods
noncomputable section
open Matrix Filter Topology Asymptotics krylov.LinearAlgebra krylov.Correction
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {a : Type*} {f : Filter a} {p : ℕ}

/-- Actual finite physical synthesis multiplies its genuine scalar and
vector orders, without any independence or nonzero-column hypothesis.
Use: error coordinates yield actual physical errors on the observed span.
Article: main_krylov, thm:local(a), finite synthesis order.
Proof: each scalar-vector product has the product order; sum finitely. -/
theorem combine_order (y : a → Fin p → E) (w : a → Fin p → ℝ) (s t : a → ℝ)
    (hy : ∀ i,(fun z => y z i) =O[f] s) (hw : ∀ i,(fun z => w z i) =O[f] t) :
    (fun z => combine (y z) (w z)) =O[f] (fun z => t z*s z) := by
  exact (IsBigO.sum (fun i (_ : i∈(Finset.univ : Finset (Fin p))) => (hw i).smul (hy i))).congr_left
    (fun z => by simp only [combine,Finset.sum_apply])

/-- A genuine spectral matrix error acting on bounded actual coordinates
retains its order in every real coordinate.
Use: no change to the source's spectral perturbation norm is made.
Article: main_krylov, thm:local(a), actual matrix action order.
Proof: reuse the spectral entry dictionary and sum the actual products. -/
theorem matrix_mulVec_order (M : a → Matrix (Fin p) (Fin p) ℝ)
    (w : a → Fin p → ℝ) (s t : a → ℝ) (hM : M =O[f] s)
    (hw : ∀ i,(fun z => w z i) =O[f] t) (i : Fin p) :
    (fun z => (M z *ᵥ w z) i) =O[f] (fun z => s z*t z) := by
  exact (IsBigO.sum (fun j (_ : j∈(Finset.univ : Finset (Fin p))) =>
    ((matrix_bigO_iff_entry M s).mp hM i j).mul (hw j))).congr_left
      (fun z => by simp only [Matrix.mulVec,dotProduct,Finset.sum_apply])

/-- True observed coordinates have the product order of their real
columns and input vector, even at singular or zero columns.
Use: propagate an actual virtual-gradient difference into its real solve.
Article: main_krylov, thm:local(a), actual coordinate order.
Proof: apply the proved real inner-product order to each actual column. -/
theorem coordinates_order (y : a → Fin p → E) (v : a → E) (s t : a → ℝ)
    (hy : ∀ i,(fun z => y z i) =O[f] s) (hv : v =O[f] t) (i : Fin p) :
    (fun z => coordinates (y z) (v z) i) =O[f] (fun z => s z*t z) :=
  inner_order _ _ _ _ (hy i) hv

/-- The genuine data-only FC solve preserves the order of two actual
input gradients near a true nonsingular observed pairing matrix.
Use: derive native direction comparisons from actual virtual gradients.
Article: main_krylov, thm:local(a), true conjugacy perturbation order.
Proof: inverse continuity bounds the real inverse pairing. Coordinates,
its actual matrix action and finite physical synthesis preserve the input
order. Exact linearity identifies this with the true direction difference. -/
theorem conjugacyDirection_difference_order (s y : a → Fin p → E) (v w : a → E)
    (S Y : Fin p → E) (hs : Tendsto s f (𝓝 S)) (hy : Tendsto y f (𝓝 Y))
    (hu : IsUnit (crossGram Y S).det) (r : a → ℝ)
    (hvw : (fun z => v z-w z) =O[f] r) :
    (fun z => conjugacyDirection (s z) (y z) (v z)-conjugacyDirection (s z) (y z) (w z)) =O[f] r := by
  have hsb (i : Fin p) : (fun z => s z i) =O[f] (fun _ => (1 : ℝ)) :=
    ((tendsto_pi_nhds.mp hs) i).isBigO_one ℝ
  have hyb (i : Fin p) : (fun z => y z i) =O[f] (fun _ => (1 : ℝ)) :=
    ((tendsto_pi_nhds.mp hy) i).isBigO_one ℝ
  have hC : Tendsto (fun z => crossGram (y z) (s z)) f (𝓝 (crossGram Y S)) := by
    have he : Tendsto (fun z (ij : Fin p × Fin p) => inner ℝ (y z ij.1) (s z ij.2)) f
        (𝓝 (fun ij : Fin p × Fin p => inner ℝ (Y ij.1) (S ij.2))) :=
      tendsto_pi_nhds.mpr fun ij => ((tendsto_pi_nhds.mp hy) ij.1).inner
        ((tendsto_pi_nhds.mp hs) ij.2)
    exact (matrixEntryEquiv p p).symm.continuousAt.tendsto.comp he
  have hunit : IsUnit (crossGram Y S) := (Matrix.isUnit_iff_isUnit_det _).mpr hu
  have hc : ContinuousAt (fun C : Matrix (Fin p) (Fin p) ℝ => C⁻¹) (crossGram Y S) := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse,hunit.unit_spec] using NormedRing.inverse_continuousAt hunit.unit
  have hi : (fun z => (crossGram (y z) (s z))⁻¹) =O[f] (fun _ => (1 : ℝ)) :=
    (hc.tendsto.comp hC).isBigO_one ℝ
  have hco (i : Fin p) : (fun z => coordinates (y z) (v z-w z) i) =O[f] r := by
    simpa only [one_mul] using coordinates_order y (fun z => v z-w z) _ _ hyb hvw i
  have hcoeff (i : Fin p) : (fun z => ((crossGram (y z) (s z))⁻¹ *ᵥ coordinates (y z) (v z-w z)) i) =O[f] r := by
    simpa only [one_mul] using matrix_mulVec_order _ _ _ _ hi hco i
  have hout : (fun z => combine (s z) ((crossGram (y z) (s z))⁻¹ *ᵥ coordinates (y z) (v z-w z))) =O[f] r := by
    simpa only [mul_one] using combine_order s _ _ _ hsb hcoeff
  apply (hvw.neg_left.add hout).congr_left
  intro z
  have hcoords : coordinates (y z) (v z-w z)=coordinates (y z) (v z)-coordinates (y z) (w z) := by
    ext i;exact inner_sub_right _ _ _
  rw [hcoords,Matrix.mulVec_sub]
  simp only [combine,Pi.sub_apply,sub_smul,Finset.sum_sub_distrib,conjugacyDirection,conjugacyCoefficients]
  abel

end
end krylov.Methods
