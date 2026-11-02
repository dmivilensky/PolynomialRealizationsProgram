import jacobi.Support.VolterraDifference
import jacobi.Support.WaveDifferenceIdentity

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
The actual original complex support polynomial satisfies the full
printed first-difference error estimate. The proof uses its genuine
Wronskian, original positive coupling and proved top-node growth.
Use: the oscillatory envelope starts its free-wave comparison with this actual transition-state difference bound; the support edge and eigenvector limits retain the original spectral polynomials.
-/
namespace jacobi.Support
noncomputable section
open Real Filter Finset jacobi.Reference jacobi.Finite
open scoped Topology

/-- The genuine complex support wave satisfies the full original first-difference error estimate on the growing half chain.
Use: the oscillatory envelope starts its free-wave comparison with this actual transition-state difference bound; the support edge and eigenvector limits retain the original spectral polynomials.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: the exact original Wronskian splits the difference error into two terms. The first uses the proved wave error and top-node difference divided by the actual positive top value. The second is bounded by summing the original reference times wave over the finite prefix and dividing by the genuine uniformly positive coupling and reference value. Both yield the same printed scaled-energy power. -/
theorem naturalWave_firstDifference {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+4→∀y:ℂ,
      ‖(naturalWave a b ha hb n (m+1) y-naturalWave a b ha hb n m y)-
          ((topValue a b ha hb n (m+1):ℂ)-topValue a b ha hb n m)‖≤
        C*volterraEnergy a b n m y*((m:ℝ)+1)^(gamma a-1)*
          cosh (sqrt (B*volterraEnergy a b n m y)) := by
  -- The original recurrence, top-node bounds and complex wave bounds are combined on one genuine common prefix.
  obtain ⟨c,C,hc,hC,hbound⟩ := topValue_bounds ha hb
  obtain ⟨D,hD,hdiff⟩ := topValue_difference ha hb
  obtain ⟨E,B₁,hE,hB₁,herr⟩ := naturalWave_difference ha hb
  obtain ⟨V,B₂,hV,hB₂,hwave⟩ := naturalWave_cosh ha hb
  obtain ⟨A,Q,hA,hQ,hcoeff⟩ := coefficient_bounds ha hb
  let B := max B₁ B₂
  have hB : 0<B := hB₁.trans_le (le_max_left _ _)
  refine ⟨E*D/c+C*V/(A*c),B,by positivity,hB,?_⟩
  filter_upwards [hbound,hdiff,herr,hwave,(tendsto_add_atTop_nat 1).eventually hcoeff,
    eventually_ge_atTop (8:ℕ)] with n hn hd he hv hac hlarge
  intro m hm y
  let x : ℝ := (m:ℝ)+1
  let w : ℝ := x^gamma a
  let u := topValue a b ha hb n
  let v := fun j => naturalWave a b ha hb n j y
  let ac : ℝ := sqrt ((naturalChain a b ha hb (n+1)).data.aSq (m+1))
  let d : ℂ := y-(cos (gamma a*step a b (n+1)):ℝ)
  let eps := volterraEnergy a b n m y
  let H := cosh (sqrt (B*eps))
  let S : ℂ := ∑j∈range (m+1),(u j:ℂ)*v j
  have hx : 0<x := by dsimp [x]; positivity
  have hw : 0<w := rpow_pos_of_pos hx _
  have hH : 0<H := cosh_pos _
  have heps : 0≤eps := by dsimp [eps,volterraEnergy]; positivity
  have hu : c*w≤u m := (hn m (by omega)).1
  have hu0 : 0<u m := (mul_pos hc hw).trans_le hu
  have hac' : A≤ac := (hac.2 (m+1) (by omega) (by omega)).1
  have hac0 : 0<ac := hA.trans_le hac'
  have hpow : x^(gamma a-1)=w/x := rpow_sub_one hx.ne' _
  have herror : ‖v m-(u m:ℂ)‖≤E*eps*w*H := by
    exact (he m (by omega) y).trans (mul_le_mul_of_nonneg_left
      (volterra_cosh_mono a b n y (le_max_left _ _) hB.le le_rfl) (by positivity))
  have hudiff : |u (m+1)-u m|≤D*(w/x) := by
    simpa only [← hpow] using hd m (by omega)
  have hsource : ‖S‖≤C*V*x*w^2*H := by
    -- Monotonicity of the genuine positive growth weight bounds every actual source term by the last one.
    calc
      _ ≤ ∑j∈range (m+1),‖(u j:ℂ)*v j‖ := norm_sum_le _ _
      _ ≤ ∑_j∈range (m+1),(C*w)*(V*w*H) := by
        apply sum_le_sum
        intro j hj
        have hj' : j≤m := by have := mem_range.mp hj; omega
        have hwj : ((j:ℝ)+1)^gamma a≤w := by
          apply rpow_le_rpow (by positivity) _ (parameter_pos ha hb).1.le
          dsimp [x]
          exact_mod_cast Nat.add_le_add_right hj' 1
        have huj : ‖(u j:ℂ)‖≤C*w := by
          have hp : 0≤u j := (naturalPolynomial_top_pos ha hb (by omega : j≤n)).le
          rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
          exact (hn j (by omega)).2.trans (mul_le_mul_of_nonneg_left hwj hC.le)
        have hvj : ‖v j‖≤V*w*H := by
          have ht := volterra_cosh_mono a b n y (le_max_right B₁ B₂) hB.le hj'
          exact (hv j (by omega) y).trans (mul_le_mul
            (mul_le_mul_of_nonneg_left hwj hV.le) ht (cosh_pos _).le (by positivity))
        rw [norm_mul]
        exact mul_le_mul huj hvj (norm_nonneg _) (by positivity)
      _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]; dsimp [x]; ring
  have hratio : ‖v m-(u m:ℂ)‖/u m≤E*eps*H/c := by
    calc
      _ ≤ (E*eps*w*H)/(c*w) := div_le_div₀ (by positivity) herror (mul_pos hc hw) hu
      _ = _ := by field_simp
  have hterm₁ : ‖((v m-(u m:ℂ))/u m)*((u (m+1):ℂ)-u m)‖≤
      (E*D/c)*eps*(w/x)*H := by
    rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu0,
      ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ (E*eps*H/c)*(D*(w/x)) := mul_le_mul hratio hudiff (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hden : A*c*w≤ac*u m := by
    calc
      _ = A*(c*w) := by ring
      _ ≤ ac*u m := mul_le_mul hac' hu (by positivity) hac0.le
  have hterm₂ : ‖d*S/((ac:ℂ)*u m)‖≤(C*V/(A*c))*eps*(w/x)*H := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hac0,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu0]
    calc
      _ ≤ (‖d‖*(C*V*x*w^2*H))/(A*c*w) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hsource (norm_nonneg _))
          (by positivity) hden
      _ = _ := by dsimp [eps,volterraEnergy,d,x] at *; field_simp
  rw [naturalWave_difference_identity a b ha hb n m (by omega) y]
  calc
    _ ≤ ‖((v m-(u m:ℂ))/u m)*((u (m+1):ℂ)-u m)‖+‖d*S/((ac:ℂ)*u m)‖ := norm_add_le _ _
    _ ≤ (E*D/c)*eps*(w/x)*H+(C*V/(A*c))*eps*(w/x)*H := add_le_add hterm₁ hterm₂
    _ = _ := by rw [hpow]; ring

end
end jacobi.Support
