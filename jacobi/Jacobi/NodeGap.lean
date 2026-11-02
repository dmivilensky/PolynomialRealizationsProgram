import jacobi.Jacobi.AngularGap
import jacobi.Jacobi.ZeroModel
import jacobi.Oscillation.NodalCosineGap

/-!
Article: jacobi, Proposition B.1.
The original two-edge angular bounds and every actual angular gap imply
the complete quadratic node-gap scale with the exact source m_(k,l).
All constants and degree thresholds depend only on alpha,beta.
Use: supplies the actual-node separation assertion in Proposition B.1 (c) and all later divided-difference and interpolation estimates.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Oscillation
open scoped Topology

/-- Every pair of actual original Jacobi nodes has the full source uniform quadratic gap, including unequal growing indices and both edges.
Use: supplies the actual-node separation assertion in Proposition B.1 (c) and all later divided-difference and interpolation estimates.
Article: jacobi, Proposition B.1.
Proof: take the smaller of the true endpoint and consecutive-gap constants.
The corrected finite angle list is monotone, giving both full-index endpoint
distances and every telescoped angular gap. Apply the proved two-sine
conversion, then identify the actual original node as its actual angle cosine.
The ordered-pair form covers arbitrary pairs by symmetry of absolute difference. -/
theorem node_gap_bound {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧
      ∀ i j : Fin n,i≤j →
        c*((j.val-i.val:ℕ):ℝ)*(pairIndex n i.val j.val:ℝ)/(frequency a b n)^2≤
          |(nodes a b ha hb n).value i-(nodes a b ha hb n).value j| := by
  -- The endpoint theorem and every gap concern the same original sorted node list; the finite conversion never reindexes its zeros.
  obtain ⟨d,_,hd,_,hends⟩ := angle_endpoint_bounds ha hb
  obtain ⟨g,hg,hgaps⟩ := angle_gap_bound ha hb
  let e := min d g
  have he : 0<e := lt_min hd hg
  refine ⟨2*e^2/Real.pi^2,by positivity,?_⟩
  filter_upwards [hends,hgaps,eventually_ge_atTop (1:ℕ)] with n hn hgn hnpos
  have hN := hn.1
  have hlo : ∀ i : Fin n,e/frequency a b n≤min (angle a b ha hb i) (Real.pi-angle a b ha hb i) := by
    intro i
    have hc : (1:ℝ)≤(min (i.val+1) (n-i.val):ℕ) := by exact_mod_cast (show 1≤min (i.val+1) (n-i.val) by omega)
    have heb : e≤d := min_le_left _ _
    calc
      _ ≤ d*(min (i.val+1) (n-i.val):ℕ)/frequency a b n := div_le_div_of_nonneg_right (by nlinarith) hN.le
      _ ≤ _ := (hn.2 i).1
  have hsteps : ∀ k : ℕ,∀ hk : k+1<n,
      e/frequency a b n≤angle a b ha hb (⟨k+1,hk⟩ : Fin n)-angle a b ha hb (⟨k,by omega⟩ : Fin n) := by
    intro k hk
    exact (div_le_div_of_nonneg_right (min_le_right d g) hN.le).trans (hgn.2 k hk)
  have hgeom := nodal_geometry hnpos
    ((hlo ⟨0,hnpos⟩).trans (min_le_left _ _))
    ((hlo ⟨n-1,by omega⟩).trans (min_le_right _ _)) hsteps
  refine ⟨hN,?_⟩
  intro i j hij
  have hc := nodal_cosine_gap he hN (fun i => ⟨(angle_properties ha hb i).1.1.le,(angle_properties ha hb i).1.2.le⟩)
    hgeom.1 hgeom.2 i j hij
  rw [(angle_properties ha hb i).2,(angle_properties ha hb j).2] at hc
  exact hc

end
end jacobi.Jacobi
