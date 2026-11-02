import jacobi.Comparison.NodeDisplacement
import jacobi.Support.WeightedSegments
import jacobi.Finite.PolynomialSegment

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
The original support-weighted polynomial products are uniformly bounded
on every actual interpolation segment, and their full target-to-support
node error has the required summable inverse-square two-edge majorant.
Both statements concern the genuine corrected support polynomials and
the actual original target and support probabilities and nodes.
Use: gramSummand_bound multiplies this genuine product bound by the independently proved actual target/support probability-ratio error.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Support jacobi.Finite jacobi.Jacobi
open scoped Topology

/-- All actual support-weighted polynomial products are uniformly bounded on their complete original node interpolation segments.
Use: gramSummand_bound multiplies this genuine product bound by the independently proved actual target/support probability-ratio error.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: multiply the two proved actual sqrt(N*w_k^0)-weighted value bounds from Appendix C.3, then use the exact positive square-root square identity to recover the original weighted product. -/
theorem supportGram_segment_product {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀i j:Fin (n+1),2*i.val≤n+1→2*j.val≤n+1→
      ∀k:Fin (n+1),∀x∈uIcc (modelNode a b (n+1) k.val) ((nodes a b ha hb (n+1)).value k),
        ((n:ℝ)+1)*(supportMeasure a b ha hb n).weight k*
          |(supportPolynomial a b ha hb n i).eval x*(supportPolynomial a b ha hb n j).eval x|≤C := by
  -- Both factors carry the same original spectral probability, so their square-root weights multiply exactly.
  obtain ⟨C,hC,hbound⟩ := supportPolynomial_segment_bounds ha hb
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  filter_upwards [hbound] with n hn
  intro i j hi hj k x hx
  let w := ((n:ℝ)+1)*(supportMeasure a b ha hb n).weight k
  have hw : 0≤w := mul_nonneg (by positivity) ((supportMeasure a b ha hb n).positive k).le
  have hp := (hn i hi k x hx).1
  have hq := (hn j hj k x hx).1
  have h := mul_le_mul hp hq (mul_nonneg (sqrt_nonneg _) (abs_nonneg _)) hC.le
  have he : w*|(supportPolynomial a b ha hb n i).eval x*(supportPolynomial a b ha hb n j).eval x|=
      (sqrt w*|(supportPolynomial a b ha hb n i).eval x|)*(sqrt w*|(supportPolynomial a b ha hb n j).eval x|) := by
    calc
      _ = (sqrt w)^2*|(supportPolynomial a b ha hb n i).eval x*(supportPolynomial a b ha hb n j).eval x| := by rw [sq_sqrt hw]
      _ = _ := by rw [abs_mul]; ring
  calc
    _ = (sqrt w*|(supportPolynomial a b ha hb n i).eval x|)*(sqrt w*|(supportPolynomial a b ha hb n j).eval x|) := he
    _ ≤ C*C := h
    _ = _ := (pow_two C).symm

/-- The full original weighted polynomial-product node displacement has a summable two-edge inverse-square bound, uniformly over both physical half-chain degrees.
Use: gramSummand_bound adds this actual T_k'' estimate to the genuine probability-ratio T_k' estimate in the proof of the uniform two-edge Gram limit.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: apply the ordinary weighted polynomial-product mean-value inequality on the whole genuine segment. Appendix C.3 supplies both actual value bounds and spectral derivative bounds. The proved original scaled node-displacement estimate controls N^2*e_k/hat_d_k, giving the stated uniform inverse-square edge and bulk error. -/
theorem supportGram_node_error {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀i j:Fin (n+1),2*i.val≤n+1→2*j.val≤n+1→
      ∀k:Fin (n+1),
        ((n:ℝ)+1)*(supportMeasure a b ha hb n).weight k*
          |(supportPolynomial a b ha hb n i).eval ((nodes a b ha hb (n+1)).value k)*
              (supportPolynomial a b ha hb n j).eval ((nodes a b ha hb (n+1)).value k)-
            (supportPolynomial a b ha hb n i).eval (modelNode a b (n+1) k.val)*
              (supportPolynomial a b ha hb n j).eval (modelNode a b (n+1) k.val)|≤
        C*(1/(edgeIndex (n+1) k.val:ℝ)^2+1/((n:ℝ)+1)^2) := by
  -- The actual weighted derivatives and actual node errors have their independently proved full spectral coverage.
  obtain ⟨A,hA,hbound⟩ := supportPolynomial_segment_bounds ha hb
  obtain ⟨B,hB,hnode⟩ := scaledNodeDisplacement_bound ha hb
  refine ⟨2*A^2*B,by positivity,?_⟩
  filter_upwards [hbound,hnode] with n hn hnb
  intro i j hi hj k
  let N : ℝ := (n:ℝ)+1
  let d : ℝ := edgeIndex (n+1) k.val
  let w := N*(supportMeasure a b ha hb n).weight k
  have hw : 0≤w := mul_nonneg (by dsimp [N]; positivity) ((supportMeasure a b ha hb n).positive k).le
  have hd : 0<d := by dsimp [d,edgeIndex]; exact_mod_cast (show 0<min (k.val+1) (n+1-k.val) by omega)
  have h := weighted_polynomial_product_change (supportPolynomial a b ha hb n i)
    (supportPolynomial a b ha hb n j) hw hA.le (by positivity : 0≤A*N^2/d)
    (fun x hx => hn i hi k x hx) (fun x hx => hn j hj k x hx)
  have he : 2*A*(A*N^2/d)*|(nodes a b ha hb (n+1)).value k-modelNode a b (n+1) k.val|=
      (2*A^2)*(N^2/d*|(nodes a b ha hb (n+1)).value k-modelNode a b (n+1) k.val|) := by ring
  rw [he] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (hnb k) (by positivity : 0≤2*A^2)).trans_eq (by ring))

end
end jacobi.Comparison
