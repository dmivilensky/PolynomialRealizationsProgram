import jacobi.Support.TransitionBounds
import jacobi.Support.OscillatoryPropagation

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The actual polynomial and first-difference transition estimates give
the genuine two-component starting state with its original power.
Use: the global support oscillatory envelope starts its actual finite propagation at floor(1/|theta|) using this proved original state bound.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference jacobi.Finite
open scoped Topology

/-- The genuine free state has the original transition-index growth power throughout every bounded scaled-frequency region.
Use: the global support oscillatory envelope starts its actual finite propagation at floor(1/|theta|) using this proved original state bound.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: each exact free difference is the original polynomial difference plus an exponential increment times the actual polynomial. The proved transition bounds and the actual linear exponential remainder bound control both terms. The same condition (m+1)*|theta|<=R changes the value term into the printed first-difference power. -/
theorem naturalState_transition {a b R:ℝ} (ha:-1<a) (hb:-1<b) (hR:0≤R) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+3→∀theta:ℂ,‖theta‖*((m:ℝ)+1)≤R→
      naturalState a b ha hb n m theta≤C*((m:ℝ)+1)^(gamma a-1) := by
  -- The original frequency and adjacent polynomial values determine both free differences exactly.
  obtain ⟨A,hA,hbound⟩ := naturalWave_transition ha hb hR
  refine ⟨2*A+2*exp R*A*R,by positivity,?_⟩
  filter_upwards [hbound] with n hn
  intro m hm theta htheta
  let x : ℝ := (m:ℝ)+1
  let v := naturalWave a b ha hb n m (Complex.cos theta)
  let w := naturalWave a b ha hb n (m+1) (Complex.cos theta)
  let q := Complex.exp (theta*Complex.I)
  have hx : 0<x := by dsimp [x]; positivity
  have hx1 : 1≤x := by dsimp [x]; linarith [Nat.cast_nonneg m (α:=ℝ)]
  have htR : ‖theta‖≤R := by nlinarith only [htheta,hx1,norm_nonneg theta]
  have hq : ‖q-1‖≤exp R*‖theta‖ := by
    have h := jacobi.Complex.exponential_increment_bound hR (z:=theta*Complex.I)
      (by simpa only [norm_mul,Complex.norm_I,mul_one] using htR)
    simpa only [q,norm_mul,Complex.norm_I,mul_one] using h
  have hqi : ‖q⁻¹-1‖≤exp R*‖theta‖ := by
    have h := jacobi.Complex.exponential_increment_bound hR (z:=-(theta*Complex.I))
      (by simpa only [norm_neg,norm_mul,Complex.norm_I,mul_one] using htR)
    simpa only [Complex.exp_neg,q,norm_neg,norm_mul,Complex.norm_I,mul_one] using h
  have hv := hn m hm theta htheta
  have hpart (z:ℂ) (hz:‖z-1‖≤exp R*‖theta‖) :
      ‖w-z*v‖≤A*x^(gamma a-1)+(exp R*‖theta‖)*(A*x^gamma a) := by
    have he : w-z*v=(w-v)+(1-z)*v := by ring
    rw [he]
    calc
      _ ≤ ‖w-v‖+‖(1-z)*v‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul,norm_sub_rev (1:ℂ) z]
        exact add_le_add hv.2 (mul_le_mul hz hv.1 (norm_nonneg _) (by positivity))
  have hscale : ‖theta‖*x^gamma a≤R*x^(gamma a-1) := by
    rw [rpow_sub_one hx.ne',← mul_div_assoc]
    apply (le_div_iff₀ hx).mpr
    have h := mul_le_mul_of_nonneg_right htheta (rpow_pos_of_pos hx (gamma a)).le
    nlinarith only [h]
  change ‖w-q*v‖+‖w-q⁻¹*v‖≤_
  have hs := add_le_add (hpart q hq) (hpart q⁻¹ hqi)
  have ht := mul_le_mul_of_nonneg_left hscale (by positivity : 0≤exp R*A)
  nlinarith only [hs,ht]

end
end jacobi.Support
