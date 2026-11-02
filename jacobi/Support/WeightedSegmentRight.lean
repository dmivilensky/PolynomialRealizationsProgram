import jacobi.Support.RealEnvelope
import jacobi.Support.WeightedPowerBounds
import jacobi.Support.PolynomialDerivative
import jacobi.Support.WeightBounds
import jacobi.Jacobi.InterpolationCoordinates

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The original corrected support polynomials and their true spectral
derivatives have the printed uniform weighted bounds on every complete
support-to-target segment. The actual weight, angular coordinate and
all coefficient and frequency estimates are independently proved.
Use: supportPolynomial_segment_bounds reflects these estimates to the whole original spectrum; the target/support Gram comparison uses them to control every original node displacement.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter Polynomial jacobi.Reference
open scoped Topology

/-- All actual right-half interpolation segments have the complete original support-weighted polynomial and spectral derivative bounds.
Use: supportPolynomial_segment_bounds reflects these estimates to the whole original spectrum; the target/support Gram comparison uses them to control every original node displacement.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: construct the genuine physical angle of each original segment point and apply the proved real support envelopes. The same actual support probability has its uniform edge power, which cancels the envelope's negative angle power. The exact affine derivative costs the inverse positive scale; the frequency is at most twice the original dimension and the sine is bounded below by its proved mesh scale. -/
theorem supportPolynomial_right_segment_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀i:Fin (n+1),2*i.val≤n+1→
      ∀k:Fin (n+1),2*k.val≤n→∀x:ℝ,
      x∈uIcc (jacobi.Jacobi.modelNode a b (n+1) k.val) ((jacobi.Jacobi.nodes a b ha hb (n+1)).value k)→
      sqrt (((n:ℝ)+1)*(supportMeasure a b ha hb n).weight k)*|(supportPolynomial a b ha hb n i).eval x|≤C ∧
      sqrt (((n:ℝ)+1)*(supportMeasure a b ha hb n).weight k)*|(supportPolynomial a b ha hb n i).derivative.eval x|≤
        C*((n:ℝ)+1)^2/(k+1:ℝ) := by
  -- Constants come from actual independent support, node and matrix estimates.
  obtain ⟨c,hc,hcoords⟩ := jacobi.Jacobi.firstHalf_interpolation_coordinates ha hb
  obtain ⟨cW,CW,hcW,hCW,hweights⟩ := supportWeight_right_bounds ha hb
  obtain ⟨A,hA,henv⟩ := naturalPolynomial_real_envelope ha hb
  let B : ℝ := sqrt CW*c^(-gamma a)
  let D : ℝ := 4*A*B/c
  have hB : 0<B := mul_pos (sqrt_pos.mpr hCW) (rpow_pos_of_pos hc _)
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨A*B+D,by positivity,?_⟩
  have hscale := (jacobi.Jacobi.modelScale_tendsto a b).eventually (Ioi_mem_nhds (by norm_num : (1/2:ℝ)<1))
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hcoords,hweights,henv,
    (tendsto_add_atTop_nat 1).eventually hscale,
    (tendsto_add_atTop_nat 1).eventually (jacobi.Jacobi.frequency_degree_comparison a b)] with n hncoords hnW hnP hsc hfreq
  intro i hi k hk x hx
  let N : ℝ := (n:ℝ)+1
  let r : ℝ := (k+1:ℝ)/N
  let w := (supportMeasure a b ha hb n).weight k
  let S := sqrt (N*w)
  have hN : 0<N := by dsimp [N]; positivity
  have hr : 0<r := div_pos (by positivity) hN
  have hw : 0<w := (supportMeasure a b ha hb n).positive k
  have hF : 0< jacobi.Jacobi.frequency a b (n+1) := jacobi.Jacobi.frequency_pos ha hb (by omega)
  have hFhi : jacobi.Jacobi.frequency a b (n+1)≤2*N := by
    simpa only [N,Nat.cast_add,Nat.cast_one] using hfreq.2.2
  have hscale' : 0< jacobi.Jacobi.modelScale a b (n+1) := by linarith
  have hx' : x∈uIcc (jacobi.Jacobi.modelNode a b (n+1) k.val)
      (cos (jacobi.Jacobi.finiteAngleAt a b ha hb (n+1) k.val)) := by
    rw [jacobi.Jacobi.finiteAngleAt_eq ha hb k.isLt,(jacobi.Jacobi.angle_properties ha hb k).2]
    exact hx
  obtain ⟨theta,ht,hxcoord,hs⟩ := hncoords.2.2 k.val (by omega) x hx'
  have hs' : c*r≤sin theta := by simpa only [r,N,Nat.cast_add,Nat.cast_one,mul_div_assoc] using hs
  have hsin : 0<sin theta := lt_of_lt_of_le (mul_pos hc hr) hs'
  have htheta : c*r≤theta := hs'.trans (sin_le ht.1.le)
  have hweight : N*w≤CW*r^(2*gamma a) := by
    have h := (hnW k.val hk).2
    have he : naturalWeight a b ha hb n k.val=w := by
      simp only [naturalWeight,dite_eq_left k.isLt]
      rfl
    rw [he] at h
    have hh := (le_div_iff₀ hN).mp h
    nlinarith only [hh]
  have hdecay : S*theta^(-gamma a)≤B :=
    weighted_power_decay hN.le hw.le hCW hr (parameter_pos ha hb).1.le hc htheta hweight
  have hraw := hnP i.val (by omega) theta ht
  have hcoord : (x- jacobi.Jacobi.modelShift a b (n+1))/ jacobi.Jacobi.modelScale a b (n+1)=cos theta := by
    rw [hxcoord]
    field_simp [hscale'.ne']
    ring
  have hvalue : S*|(supportPolynomial a b ha hb n i).eval x|≤A*B := by
    rw [supportPolynomial_eval,hcoord]
    calc
      _ ≤ S*(A*theta^(-gamma a)) := mul_le_mul_of_nonneg_left hraw.1 (sqrt_nonneg _)
      _ = A*(S*theta^(-gamma a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdecay hA.le
  -- The exact inverse sine and affine scale account for the full printed n^2/(k+1) derivative factor.
  have hinv : 1/sin theta≤N/(c*(k+1:ℝ)) := by
    calc
      _ ≤ 1/(c*(k+1:ℝ)/N) := one_div_le_one_div_of_le (div_pos (mul_pos hc (by positivity)) hN)
        (by simpa only [r,mul_div_assoc] using hs')
      _ = _ := by field_simp
  have hderiv : S*|(naturalPolynomial a b ha hb n i.val).derivative.eval (cos theta)|≤
      (2*A*B/c)*N^2/(k+1:ℝ) := by
    calc
      _ ≤ S*(A* jacobi.Jacobi.frequency a b (n+1)*theta^(-gamma a)/sin theta) :=
        mul_le_mul_of_nonneg_left hraw.2 (sqrt_nonneg _)
      _ = (A* jacobi.Jacobi.frequency a b (n+1))*(S*theta^(-gamma a))/sin theta := by ring
      _ ≤ (A* jacobi.Jacobi.frequency a b (n+1))*B/sin theta := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdecay (mul_pos hA hF).le) hsin.le
      _ ≤ (A*(2*N))*B/sin theta := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFhi hA.le) hB.le) hsin.le
      _ = (A*(2*N)*B)*(1/sin theta) := by ring
      _ ≤ (A*(2*N)*B)*(N/(c*(k+1:ℝ))) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  have hderiv' : S*|(supportPolynomial a b ha hb n i).derivative.eval x|≤D*N^2/(k+1:ℝ) := by
    rw [supportPolynomial_derivative_eval,hcoord,abs_div,abs_of_pos hscale']
    calc
      _ = (S*|(naturalPolynomial a b ha hb n i.val).derivative.eval (cos theta)|)/ jacobi.Jacobi.modelScale a b (n+1) := by ring
      _ ≤ ((2*A*B/c)*N^2/(k+1:ℝ))/ jacobi.Jacobi.modelScale a b (n+1) :=
        div_le_div_of_nonneg_right hderiv hscale'.le
      _ ≤ ((2*A*B/c)*N^2/(k+1:ℝ))/(1/2:ℝ) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hsc.le
      _ = _ := by dsimp [D]; ring
  exact ⟨hvalue.trans (le_add_of_nonneg_right hD.le),
    hderiv'.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (mul_pos hA hB).le) (sq_nonneg N)) (by positivity))⟩

end
end jacobi.Support
