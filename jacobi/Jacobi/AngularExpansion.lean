import jacobi.Jacobi.SecondOrderComparison
import jacobi.Jacobi.AngularCorrection

/-!
Article: jacobi, Proposition B.1.
The actual uniformly numbered finite zeros have precisely the printed
cotangent/tangent correction and both original error terms. The proof
combines the genuine phase-to-zero comparison, true McMahon theorem and
actual regular-primitive Lipschitz estimate. Every small index is included.
Use: the printed part (a) and the corrected cosine-model error of Proposition B.1 (b).
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- All original first-half finite Jacobi angles satisfy their exact source correction and uniform two-term error, including every small index.
Use: the printed part (a) and the corrected cosine-model error of Proposition B.1 (b).
Article: jacobi, Proposition B.1.
Proof: for the actual large-index prefix combine the genuine corrected
Bessel comparison with McMahon and replace R(theta) by R(x) using the
proved original Lipschitz bound and coarse angular error. The three
literal errors are O(N^(-3)), O(1/(N*k^3)) and O(1/(N^3*k)).
The finite remaining indices are absorbed using the already proved
coarse original angle and actual correction bounds. -/
theorem firstHalf_angle_expansion {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧
      ∀ k,2*k<n →
        |finiteAngleAt a b ha hb n k-modelAngle a b n k-modelCorrection a b n k|≤
          C*(1/(frequency a b n*(k+1:ℝ)^3)+1/(frequency a b n)^3) := by
  -- The only asymptotic inputs are the proved actual original zero theorems; no source expansion is introduced as a hypothesis or certificate.
  obtain ⟨k1,S,hS,hsecond⟩ := firstHalf_bessel_second_order ha hb
  obtain ⟨M,hM,hmc⟩ := mcmahon ha
  obtain ⟨A,hA,hcoarse⟩ := firstHalf_angle_coarse ha hb
  obtain ⟨B,hB,hcorr⟩ := firstHalf_modelCorrection_bound ha hb
  obtain ⟨P,hP,hpot⟩ := regularPotential_C1_bound a b
  let C := M+S+P*A+(A+B)*(k1+1:ℝ)^2+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hsecond,hcoarse,hcorr,firstHalf_angle_cap ha hb,firstHalf_modelAngle_cap a b] with n hs hc hd hcap hmodel
  have hN := hs.1
  refine ⟨hN,?_⟩
  intro k hk
  let N := frequency a b n
  let t : ℝ := k+1
  let theta := finiteAngleAt a b ha hb n k
  let x := modelAngle a b n k
  let j := positiveZero a ha k
  let v := phaseGrid a k
  have ht : 0<t := by dsimp [t]; positivity
  have ht1 : 1≤t := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hx := (modelAngle_endpoint_bounds ha hb (show k<n by omega)).1
  have hv : 0<v := phaseGrid_pos ha k
  by_cases hkk : k1≤k
  · have h1 := hs.2 k hkk hk
    have h2 := div_le_div_of_nonneg_right (hmc k) hN.le
    have hr := regularPrimitive_lipschitz a b P (fun y hy => (hpot y hy).1)
      ⟨hx.1.le,hmodel.2 k hk⟩ ⟨(finiteAngleAt_interval ha hb (show k<n by omega)).1.le,hcap k hk⟩
    have hrbound : |regularPrimitive a b x-regularPrimitive a b theta|≤P*(A/(N*t)) := by
      rw [abs_sub_comm]
      exact hr.trans (mul_le_mul_of_nonneg_left (hc.2 k hk) hP.le)
    have h3 : |(regularPrimitive a b x-regularPrimitive a b theta)/(2*N^2)|≤(P*A/2)/N^3 := by
      rw [abs_div,abs_of_pos (by positivity : 0<2*N^2)]
      calc
        _ ≤ (P*(A/(N*t)))/(2*N^2) := div_le_div_of_nonneg_right hrbound (by positivity)
        _ = ((P*A/2)/N^3)/t := by field_simp [hN.ne',ht.ne']
        _ ≤ _ := div_le_self (by positivity) ht1
    have he : theta-x-modelCorrection a b n k=
        (theta-j/N+regularPrimitive a b theta/(2*N^2))+
          ((j-v-(1/4-a^2)/(2*v))/N)+
          ((regularPrimitive a b x-regularPrimitive a b theta)/(2*N^2)) := by
      dsimp [modelCorrection,endpointCorrection,theta,x,j,v,modelAngle,N]
      field_simp [hN.ne',hv.ne']
      ring
    change |theta-x-modelCorrection a b n k|≤C*(1/(N*t^3)+1/N^3)
    rw [he]
    have h2' : |(j-v-(1/4-a^2)/(2*v))/N|≤M/(N*t^3) := by
      rw [abs_div,abs_of_pos hN]
      calc
        _ ≤ (M/t^3)/N := h2
        _ = _ := by rw [div_div]; congr 1; ring
    calc
      _ ≤ |theta-j/N+regularPrimitive a b theta/(2*N^2)|+
        |(j-v-(1/4-a^2)/(2*v))/N|+|(regularPrimitive a b x-regularPrimitive a b theta)/(2*N^2)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ S/N^3+M/(N*t^3)+(P*A/2)/N^3 := add_le_add (add_le_add h1 h2') h3
      _ ≤ C/N^3+C/(N*t^3) := by
        have hCM : M≤C := by
          have hh : 0≤(A+B)*(k1+1:ℝ)^2 := by positivity
          have hp : 0≤P*A := by positivity
          dsimp [C]
          linarith
        have hCS : S+P*A/2≤C := by
          dsimp [C]
          nlinarith [mul_nonneg hP.le hA.le,sq_nonneg (k1+1:ℝ)]
        have hh1 := div_le_div_of_nonneg_right hCM (show 0≤N*t^3 by positivity)
        have hh2 := div_le_div_of_nonneg_right hCS (show 0≤N^3 by positivity)
        have hid : S/N^3+(P*A/2)/N^3=(S+P*A/2)/N^3 := by ring
        rw [← hid] at hh2
        linarith
      _ = _ := by ring
  · have hraw : |theta-x-modelCorrection a b n k|≤(A+B)/(N*t) := by
      calc
        _ ≤ |theta-x|+|modelCorrection a b n k| := abs_sub _ _
        _ ≤ A/(N*t)+B/(N*t) := add_le_add (hc.2 k hk) (hd.2 k hk)
        _ = _ := by ring
    have htK : t≤(k1+1:ℝ) := by
      have hh : k≤k1 := by omega
      dsimp [t]
      exact_mod_cast Nat.add_le_add_right hh 1
    have hsmall : (A+B)/(N*t)≤((A+B)*(k1+1:ℝ)^2)/(N*t^3) := by
      have hsq := (sq_le_sq₀ ht.le (by positivity : 0≤(k1+1:ℝ))).mpr htK
      have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (show 0≤A+B by positivity)) (show 0≤N*t^3 by positivity)
      convert hh using 1
      field_simp [hN.ne',ht.ne']
    have hCC : (A+B)*(k1+1:ℝ)^2≤C := by
      have hp : 0≤P*A := by positivity
      dsimp [C]
      linarith
    have hh := div_le_div_of_nonneg_right hCC (show 0≤N*t^3 by positivity)
    have hpos : 0≤C/N^3 := by positivity
    calc
      _ ≤ (A+B)/(N*t) := hraw
      _ ≤ C/(N*t^3) := hsmall.trans hh
      _ ≤ C*(1/(N*t^3)+1/N^3) := by
        have he : C*(1/(N*t^3)+1/N^3)=C/(N*t^3)+C/N^3 := by ring
        rw [he]
        linarith

/-- The complete printed original angular zero estimate, with its literal cotangent and tangent ratios and both uniform error terms.
Use: supplies Proposition B.1 (a) directly, without auxiliary phase or comparison premises.
Article: jacobi, Proposition B.1.
Proof: replace the proved genuine primitive correction by its exact printed half-angle expression in the unconditional angular expansion. -/
theorem zeros_angular_expansion {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧ ∀ k,2*k<n →
      |finiteAngleAt a b ha hb n k-modelAngle a b n k-
        (endpointCorrection a*(cos (modelAngle a b n k/2)/sin (modelAngle a b n k/2))-
          endpointCorrection b*(sin (modelAngle a b n k/2)/cos (modelAngle a b n k/2)))/(4*(frequency a b n)^2)|≤
            C*(1/(frequency a b n*(k+1:ℝ)^3)+1/(frequency a b n)^3) := by
  obtain ⟨C,hC,h⟩ := firstHalf_angle_expansion ha hb
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with n hn
  refine ⟨hn.1,?_⟩
  intro k hk
  rw [← modelCorrection_eq ha hb (show k<n by omega)]
  exact hn.2 k hk

end
end jacobi.Jacobi
