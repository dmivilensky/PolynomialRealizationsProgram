import krylov.LinearAlgebra.PositiveDescent
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), genuine positive shifted-pivot lower barrier.
Use: exclude the unstable actual Jacobi pivot branch using genuine positivity of every original shifted principal pivot.
Source: exact scalar Riccati recurrence, actual limiting Jacobi coefficients and the proved true positive-sequence descent contradiction.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Filter
open scoped Topology

/-- A genuine Riccati pivot below the actual strict lower barrier has a true fixed positive descent when the real coefficient defects are small.
Use: A genuine Riccati pivot below the actual strict lower barrier has a true fixed positive descent when the real coefficient defects are small.
Article: main_krylov, prop:phi(c), genuine positive shifted-pivot lower barrier.
Proof: Compare the actual squared gap with the genuine coefficient errors before dividing by the true positive current pivot. -/
theorem riccati_barrier_step (b c delta eta z w A B : ℝ)
    (hcb : c<b) (hd : 0≤delta) (heta : 0≤eta)
    (hz : 0 < z) (hzc : z<c) (hA : A≤2*b+delta) (hB : b^2-delta≤B)
    (hrec : z*w=z*A-B) (hgap : delta*(c+1)+eta*c≤(b-c)^2) :
    w≤z-eta := by
  -- The actual gap between the limiting edge and the true current pivot dominates both genuine coefficient defects.
  have h1 := mul_le_mul_of_nonneg_left hA hz.le
  have h2 := mul_le_mul_of_nonneg_left hzc.le hd
  have h3 := mul_le_mul_of_nonneg_left hzc.le heta
  have hs : (b-c)^2≤(b-z)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hzc.le) (show 0≤2*b-c-z by linarith)]
  apply le_of_mul_le_mul_left _ hz

  nlinarith

/-- Every genuinely positive Riccati pivot sequence with true limiting band-edge Jacobi coefficients eventually lies above every actual strict sub-edge barrier.
Use: Every genuinely positive Riccati pivot sequence with true limiting band-edge Jacobi coefficients eventually lies above every actual strict sub-edge barrier.
Article: main_krylov, prop:phi(c), genuine positive shifted-pivot lower barrier.
Proof: Choose genuine coefficient defect bounds; a true barrier violation would force a fixed actual descent forever, contradicting real pivot positivity. -/
theorem positive_riccati_eventual_lower (s A B : ℕ → ℝ) (b : ℝ)
    (hs : ∀ n,0 < s n) (hrec : ∀ n,s (n+1)=A (n+1)-(B n)^2/s n)
    (hA : Tendsto A atTop (𝓝 (2*b))) (hB : Tendsto B atTop (𝓝 b))
    (c : ℝ) (hc : 0 < c) (hcb : c<b) :
    ∀ᶠ n in atTop,c≤s n := by
  -- Choose genuine positive margins from the actual strict sub-edge barrier.
  let delta := (b-c)^2/(2*(c+1))
  let eta := (b-c)^2/(2*c)
  have hbc : 0 < (b-c)^2 := sq_pos_of_pos (sub_pos.mpr hcb)
  have hd : 0 < delta := by dsimp only [delta];positivity
  have he : 0 < eta := by dsimp only [eta];positivity
  have hgap : delta*(c+1)+eta*c=(b-c)^2 := by
    dsimp only [delta,eta]
    field_simp
    ring
  have ha := (tendsto_order.mp (hA.comp (tendsto_add_atTop_nat 1))).2 (2*b+delta) (by linarith)
  have hbs := (tendsto_order.mp (hB.pow 2)).1 (b^2-delta) (by linarith)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ha.and hbs)
  -- A genuine barrier violation propagates along the actual Riccati sequence and contradicts positive-pivot descent.
  refine eventually_atTop.mpr ⟨N,positive_sequence_no_descent s hs c eta he N ?_⟩
  intro n hn hsc
  have hr : s n*s (n+1)=s n*A (n+1)-(B n)^2 := by
    rw [hrec]
    field_simp [(hs n).ne']
  exact riccati_barrier_step b c delta eta (s n) (s (n+1)) (A (n+1)) ((B n)^2)
    hcb hd.le he.le (hs n) hsc (hN n hn).1.le (hN n hn).2.le hr hgap.le
end
end krylov.LinearAlgebra
