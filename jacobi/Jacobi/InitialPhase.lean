import jacobi.Jacobi.ScaledNumbering
import jacobi.Jacobi.ScaledRemainder
import jacobi.Oscillation.PhaseMeanValue

/-!
Article: jacobi, Proposition B.1.
A true finite phase based at its original kth zero is evaluated at the
same fixed Bessel argument. The already proved quantitative original
zero comparison makes their initial discrepancy small. The estimate
below uses only genuine source derivatives on their actual joining interval.
Use: places the first later original finite zero beyond a fixed common phase anchor, without a zero-numbering assumption.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Oscillation
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual scaled original finite zeros have their genuine fixed-index Bessel limit at the original Jacobi frequency.
Use: places the first later original finite zero beyond a fixed common phase anchor, without a zero-numbering assumption.
Article: jacobi, Proposition B.1.
Proof: N*theta=n*theta+((alpha+beta+1)/2)*theta. The proved genuine angular Mehler--Heine limit evaluates the first term and the actual angle tends to zero. -/
theorem scaledAngle_tendsto {a b : ℝ} (ha : -1<a) (hb : -1<b) (k : ℕ) :
    Tendsto (fun n : ℕ => scaledAngle a b ha hb n k) atTop (𝓝 (jacobi.Bessel.positiveZero a ha k)) := by
  have h := (finiteAngleAt_scaled_tendsto ha hb k).add
    ((finiteAngleAt_tendsto_zero ha hb k).const_mul ((a+b+1)/2))
  simp only [mul_zero,add_zero] at h
  convert h using 1
  ext n
  dsimp [scaledAngle,frequency]
  ring

/-- The true original finite phase at a fixed positive argument is controlled by the actual displacement of its genuine base zero.
Use: discharges the small initial phase discrepancy required by the uniform averaging theorem for the actual Jacobi solution.
Article: jacobi, Proposition B.1.
Proof: the actual unordered joining interval lies between s/2 and
3*pi*N/4. There the true phase derivative has its proved original
inverse-square form and its actual regular perturbation is at most one.
Apply the genuine phase mean-value bound and its exact base value zero. -/
theorem scaledPhase_initial_bound {a b C s : ℝ} (ha : -1<a) (hb : -1<b)
    (hbound : ∀ t∈Icc 0 (3*Real.pi/4),|regularPotential a b t|≤C)
    {n k : ℕ} (hN : 0<frequency a b n) (hk : k<n) (hs : 0<s)
    (hsupper : s/frequency a b n≤3*Real.pi/4)
    (hbaselo : s/2≤scaledAngle a b ha hb n k)
    (hbasecap : finiteAngleAt a b ha hb n k≤3*Real.pi/4)
    (heps : C/(frequency a b n)^2≤1) :
    |scaledPhase a b ha hb n hN (scaledAngle a b ha hb n k) s|≤
      (2+|endpointCorrection a|/(s/2)^2)*|s-scaledAngle a b ha hb n k| := by
  -- The phase is the original state integral based at the genuine finite zero, so its actual base value is exactly zero.
  let N := frequency a b n
  let Y := scaledAngle a b ha hb n k
  let f := scaledPhase a b ha hb n hN Y
  have hbase := scaledAngle_zero ha hb hN hk
  have hsN : s≤(3*Real.pi/4)*N := (div_le_iff₀ hN).mp hsupper
  have hYN : Y≤(3*Real.pi/4)*N := by
    dsimp [Y,scaledAngle,N]
    nlinarith [mul_le_mul_of_nonneg_left hbasecap hN.le]
  have hbox : ∀ x∈uIcc Y s,x∈Icc (s/2) ((3*Real.pi/4)*N) := by
    intro x hx
    exact (convex_Icc (s/2) ((3*Real.pi/4)*N)).ordConnected.uIcc_subset
      ⟨hbaselo,hYN⟩ ⟨by linarith,hsN⟩ hx
  have htheta : ∀ x∈uIcc Y s,x/N∈Icc 0 (3*Real.pi/4) := by
    intro x hx
    have hh := hbox x hx
    exact ⟨(div_pos (by linarith [hh.1] : 0<x) hN).le,(div_le_iff₀ hN).mpr hh.2⟩
  have hphys : ∀ x∈uIcc Y s,x∈Ioo 0 (N*Real.pi) := by
    intro x hx
    have hh := hbox x hx
    exact ⟨by linarith [hh.1],by nlinarith [hh.2,mul_pos hN Real.pi_pos]⟩
  have h := phase_lipschitz_bound (f := f) (e := scaledRemainder a b N) (c := endpointCorrection a)
    (epsilon := 1) (show 0<s/2 by linarith) (fun x hx => (hbox x hx).1)
    (fun x hx => scaledPhase_hasDerivAt ha hb n hN hbase.1 (hphys x hx) hbase.2)
    (by
      intro x hx
      dsimp [scaledRemainder]
      rw [abs_div,abs_of_pos (sq_pos_of_pos hN)]
      exact (div_le_div_of_nonneg_right (hbound (x/N) (htheta x hx)) (sq_nonneg N)).trans heps)
  have hz : f Y=0 := (scaledState a b ha hb n hN).phase_self Y
  rw [hz,sub_zero] at h
  convert h using 1
  ring

end
end jacobi.Jacobi
