import krylov.Methods.DirectBroydenIncrement
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), actual quadratic direct-update bound.
Use: propagate genuine old secant errors and scalar model errors through
the literal native direct update, retaining all actual observed pairings.
Source: true rank-update identities and the standard norm big-O calculus.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
open Filter Topology Asymptotics
open scoped InnerProductSpace
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine direct correction vector and old curvature stay bounded
from bounds on the actual primitive model, pair and two inverse curvatures.
Use: actual update estimates use the native correction vector, without
assuming a bounded vector coefficient or a bounded updated model.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: actual operator application bounds the old action, real inner
products bound its curvature and the literal vector formula has two
products of genuinely bounded native factors. -/
theorem directBroydenVector_bigO_one {l : Filter α} (B : α → E →L[ℝ] E)
    (s y : α → E) (hB : B =O[l] (fun _ => (1 : ℝ)))
    (hs : s =O[l] (fun _ => (1 : ℝ))) (hy : y =O[l] (fun _ => (1 : ℝ)))
    (ha : (fun z => (inner ℝ (s z) (B z (s z)))⁻¹) =O[l] (fun _ => (1 : ℝ)))
    (hb : (fun z => (inner ℝ (s z) (y z))⁻¹) =O[l] (fun _ => (1 : ℝ))) :
    (fun z => inner ℝ (s z) (B z (s z))) =O[l] (fun _ => (1 : ℝ)) ∧
    (fun z => directBroydenVector (B z).toLinearMap (s z) (y z)) =O[l] (fun _ => (1 : ℝ)) := by
  have hBs : (fun z => B z (s z)) =O[l] (fun _ => (1 : ℝ)) := by
    simpa only [one_mul] using clm_apply_bigO B s _ _ hB hs
  constructor
  · simpa only [one_mul] using real_inner_bigO s (fun z => B z (s z)) _ _ hs hBs
  · simpa only [one_smul,directBroydenVector,ContinuousLinearMap.coe_coe] using (hb.smul hy).sub (ha.smul hBs)

/-- A true direct correction-vector cross pairing is first order whenever
the two genuine new pair cross pairings are first order.
Use: derive the native interpolation cross error inside every actual
old scalar model update, without assuming the desired quadratic bound.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: real old model symmetry identifies its actual cross pairing;
expand the genuine correction vector and multiply by the two actual
bounded inverse curvature factors. -/
theorem directBroydenVector_pairing_bigO {l : Filter α} (B : α → E →L[ℝ] E)
    (s y u : α → E) (t : α → ℝ)
    (hsym : ∀ᶠ z in l,(B z).toLinearMap.IsSymmetric)
    (ha : (fun z => (inner ℝ (s z) (B z (s z)))⁻¹) =O[l] (fun _ => (1 : ℝ)))
    (hb : (fun z => (inner ℝ (s z) (y z))⁻¹) =O[l] (fun _ => (1 : ℝ)))
    (hBu : (fun z => inner ℝ (s z) (B z (u z))) =O[l] t)
    (hyu : (fun z => inner ℝ (y z) (u z)) =O[l] t) :
    (fun z => inner ℝ (directBroydenVector (B z).toLinearMap (s z) (y z)) (u z)) =O[l] t := by
  have he : (fun z => inner ℝ (directBroydenVector (B z).toLinearMap (s z) (y z)) (u z))
      =ᶠ[l] (fun z => (inner ℝ (s z) (y z))⁻¹*inner ℝ (y z) (u z)-
        (inner ℝ (s z) (B z (s z)))⁻¹*inner ℝ (s z) (B z (u z))) := by
    filter_upwards [hsym] with z hz
    simp only [directBroydenVector,inner_sub_left,real_inner_smul_left,ContinuousLinearMap.coe_coe]
    have h : inner ℝ (B z (s z)) (u z)=inner ℝ (s z) (B z (u z)) := hz (s z) (u z)
    rw [h]
  have h : (fun z => (inner ℝ (s z) (y z))⁻¹*inner ℝ (y z) (u z)-
      (inner ℝ (s z) (B z (s z)))⁻¹*inner ℝ (s z) (B z (u z))) =O[l] t := by
    simpa only [one_mul] using (hb.mul hyu).sub (ha.mul hBu)
  exact h.congr' he.symm EventuallyEq.rfl

/-- Every literal direct update changes an actual old vector secant by
only first order from genuine first-order cross pairings.
Use: close the native vector-secant induction in the source comparison.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: derive the true bounded old action, curvature and correction vector.
Each term of the actual vector update contains one true first-order cross
pairing and otherwise only genuine bounded native coefficients. -/
theorem directBroydenOperatorUpdate_vector_bigO {l : Filter α} (B : α → E →L[ℝ] E)
    (s y u : α → E) (phi t : α → ℝ)
    (hsym : ∀ᶠ z in l,(B z).toLinearMap.IsSymmetric)
    (hB : B =O[l] (fun _ => (1 : ℝ))) (hs : s =O[l] (fun _ => (1 : ℝ)))
    (hy : y =O[l] (fun _ => (1 : ℝ))) (hphi : phi =O[l] (fun _ => (1 : ℝ)))
    (ha : (fun z => (inner ℝ (s z) (B z (s z)))⁻¹) =O[l] (fun _ => (1 : ℝ)))
    (hb : (fun z => (inner ℝ (s z) (y z))⁻¹) =O[l] (fun _ => (1 : ℝ)))
    (hBu : (fun z => inner ℝ (s z) (B z (u z))) =O[l] t)
    (hyu : (fun z => inner ℝ (y z) (u z)) =O[l] t) :
    (fun z => directBroydenOperatorUpdate (B z) (s z) (y z) (phi z) (u z)-B z (u z)) =O[l] t := by
  have hBs := clm_apply_bigO B s _ _ hB hs
  have hv := directBroydenVector_bigO_one B s y hB hs hy ha hb
  have hcross := directBroydenVector_pairing_bigO B s y u t hsym ha hb hBu hyu
  have h1 := ((ha.neg_left.mul hBu).smul hBs)
  have h2 := ((hb.mul hyu).smul hy)
  have h3 := (((hphi.mul hv.1).mul hcross).smul hv.2)
  simp only [one_mul,mul_one,smul_eq_mul] at h1 h2 h3
  simpa only [directBroydenOperatorUpdate_change] using (h1.add h2).add h3

/-- Every genuine old scalar model entry changes by second order under
the actual direct Broyden update when its real cross pairings are first order.
Use: this is the literal quadratic update estimate of the original
chronological Broyden comparison, valid for arbitrary bounded schedules.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: derive both true correction-vector pairings. Each exact scalar
rank-update term has two first-order factors and genuine bounded native
curvature/interpolation factors, so all three terms have quadratic order. -/
theorem directBroydenOperatorUpdate_scalar_bigO {l : Filter α} (B : α → E →L[ℝ] E)
    (s y u w : α → E) (phi t : α → ℝ)
    (hsym : ∀ᶠ z in l,(B z).toLinearMap.IsSymmetric)
    (hB : B =O[l] (fun _ => (1 : ℝ))) (hs : s =O[l] (fun _ => (1 : ℝ)))
    (hy : y =O[l] (fun _ => (1 : ℝ))) (hphi : phi =O[l] (fun _ => (1 : ℝ)))
    (ha : (fun z => (inner ℝ (s z) (B z (s z)))⁻¹) =O[l] (fun _ => (1 : ℝ)))
    (hb : (fun z => (inner ℝ (s z) (y z))⁻¹) =O[l] (fun _ => (1 : ℝ)))
    (hBu : (fun z => inner ℝ (s z) (B z (u z))) =O[l] t)
    (hBw : (fun z => inner ℝ (s z) (B z (w z))) =O[l] t)
    (hyu : (fun z => inner ℝ (y z) (u z)) =O[l] t)
    (hyw : (fun z => inner ℝ (y z) (w z)) =O[l] t) :
    (fun z => inner ℝ (u z) (directBroydenOperatorUpdate (B z) (s z) (y z) (phi z) (w z))-
      inner ℝ (u z) (B z (w z))) =O[l] (fun z => t z^2) := by
  have hv := directBroydenVector_bigO_one B s y hB hs hy ha hb
  have hcu := directBroydenVector_pairing_bigO B s y u t hsym ha hb hBu hyu
  have hcw := directBroydenVector_pairing_bigO B s y w t hsym ha hb hBw hyw
  have h1 := (ha.neg_left.mul hBw).mul hBu
  have h2 := (hb.mul hyw).mul hyu
  have h3 := ((hphi.mul hv.1).mul hcw).mul hcu
  simp only [one_mul] at h1 h2 h3
  have h := (h1.add h2).add h3
  have h' : (fun z => -(inner ℝ (s z) (B z (s z)))⁻¹*inner ℝ (s z) (B z (w z))*inner ℝ (s z) (B z (u z))+
      (inner ℝ (s z) (y z))⁻¹*inner ℝ (y z) (w z)*inner ℝ (y z) (u z)+
      (phi z*inner ℝ (s z) (B z (s z)))*inner ℝ (directBroydenVector (B z).toLinearMap (s z) (y z)) (w z)*
        inner ℝ (directBroydenVector (B z).toLinearMap (s z) (y z)) (u z)) =O[l] (fun z => t z^2) := by
    simpa only [← sq] using h
  apply h'.congr' ?_ EventuallyEq.rfl
  filter_upwards [hsym] with z hz
  exact (directBroydenOperatorUpdate_pairing_change _ hz _ _ _ _ _).symm

end
end krylov.Methods
