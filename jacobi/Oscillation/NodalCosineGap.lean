import jacobi.Oscillation.NodalGeometry

/-!
Article: jacobi, Proposition B.1.
The true finite endpoint distances and telescoped angular gaps imply the
exact difference-times-sum-of-indices lower bound. This common scalar
lemma applies to both the original Jacobi spectrum and its explicit
trigonometric model.
Use: discharges the geometric conversion for both original-node and model-node assertions of Proposition B.1 (c).
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set

/-- A genuine finite principal-angle list with full-index endpoint and gap bounds has the exact uniform quadratic cosine-gap scale.
Use: discharges the geometric conversion for both original-node and model-node assertions of Proposition B.1 (c).
Article: jacobi, Proposition B.1.
Proof: the actual midpoint has distance at least d*m/(2*N) from either
endpoint by summing the original two index-weighted distances. Apply
the two-sine cosine-gap estimate and the full-index angular gap bound.
All minimum and difference indices are the literal finite source indices. -/
theorem nodal_cosine_gap {n : ℕ} {f : Fin n → ℝ} {d N : ℝ} (hd : 0<d) (hN : 0<N)
    (hf : ∀ i,f i∈Icc 0 Real.pi)
    (hends : ∀ i,d*(i.val+1:ℝ)/N≤f i ∧ d*((n-i.val:ℕ):ℝ)/N≤Real.pi-f i)
    (hspan : ∀ i j : Fin n,i≤j → d*((j.val-i.val:ℕ):ℝ)/N≤f j-f i)
    (i j : Fin n) (hij : i≤j) :
    (2*d^2/Real.pi^2)*((j.val-i.val:ℕ):ℝ)*((min (i.val+j.val+2) (2*n-i.val-j.val):ℕ):ℝ)/N^2≤
      |cos (f i)-cos (f j)| := by
  -- The midpoint sum, rather than only the smaller individual index, retains the full source m_(k,l) weight for widely separated nodes.
  let m := min (i.val+j.val+2) (2*n-i.val-j.val)
  have hm0 : (0:ℝ)≤(m:ℝ) := Nat.cast_nonneg m
  have hmL : (m:ℝ)≤(i.val:ℝ)+j.val+2 := by
    exact_mod_cast min_le_left (i.val+j.val+2) (2*n-i.val-j.val)
  have hmR : (m:ℝ)≤((n-i.val:ℕ):ℝ)+((n-j.val:ℕ):ℝ) := by
    have he : 2*n-i.val-j.val=(n-i.val)+(n-j.val) := by omega
    have hh := min_le_right (i.val+j.val+2) (2*n-i.val-j.val)
    dsimp [m]
    rw [he]
    rw [he] at hh
    exact_mod_cast hh
  have hlo : d*(m:ℝ)/N≤f i+f j := by
    calc
      _ ≤ d*((i.val:ℝ)+j.val+2)/N := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmL hd.le) hN.le
      _ = d*(i.val+1:ℝ)/N+d*(j.val+1:ℝ)/N := by ring
      _ ≤ _ := add_le_add (hends i).1 (hends j).1
  have hhi : d*(m:ℝ)/N≤2*Real.pi-f i-f j := by
    calc
      _ ≤ d*(((n-i.val:ℕ):ℝ)+((n-j.val:ℕ):ℝ))/N := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmR hd.le) hN.le
      _ = d*((n-i.val:ℕ):ℝ)/N+d*((n-j.val:ℕ):ℝ)/N := by ring
      _ ≤ _ := by linarith [(hends i).2,(hends j).2]
  have hgap := hspan i j hij
  have horder : f i≤f j := by
    have hz : 0≤d*((j.val-i.val:ℕ):ℝ)/N := by positivity
    linarith
  have hc := cosine_gap_lower (hf i) (hf j) horder (by positivity : 0≤d*(m:ℝ)/N) hlo hhi
  have hh := mul_le_mul_of_nonneg_left hgap (show 0≤2*(d*(m:ℝ)/N)/Real.pi^2 by positivity)
  calc
    _ = (2*(d*(m:ℝ)/N)/Real.pi^2)*(d*((j.val-i.val:ℕ):ℝ)/N) := by field_simp [hN.ne']; ring
    _ ≤ (2*(d*(m:ℝ)/N)/Real.pi^2)*(f j-f i) := hh
    _ ≤ _ := by convert hc using 1; ring

end
end jacobi.Oscillation
