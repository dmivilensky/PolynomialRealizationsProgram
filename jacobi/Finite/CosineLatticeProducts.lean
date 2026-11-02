import jacobi.Finite.PuncturedProducts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The absolute characteristic derivative on a cosine lattice factors into
the sum-angle sine product and the two distance products. No asymptotic
estimate or support-weight formula is assumed in this calculation.
Source: the cosine subtraction identity and elementary finite products.
Use: cosine_lattice_product evaluates the distance half of the actual characteristic-gap product before obtaining the support-weight ratio.
-/
namespace jacobi.Finite
noncomputable section
open Real Finset

/-- The positive sine distance on an angular lattice, with the diagonal omitted.
Use: cosine_lattice_product evaluates the distance half of the actual characteristic-gap product before obtaining the support-weight ratio.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
-/
def sineDistanceProduct (h : ℝ) (n k : ℕ) : ℝ :=
  ∏j∈(range (n+1)).erase k,sin (|(k:ℝ)-j| *h/2)

/-- The product of the first positive half-step sines.
Use: sineDistanceProduct_eq and its adjacent-index cancellation leave the two endpoint factors in the support-weight formula.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
-/
def sineFactorial (h : ℝ) (m : ℕ) : ℝ :=
  ∏j∈range m,sin (((j:ℝ)+1)*h/2)

/-- The distance product splits into the same two positive sine factorials on either side of the omitted node.
Use: cosine_lattice_product separates the index dependence of the actual cosine characteristic derivative.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: split at the omitted point; reflect the left interval and translate the right interval. The absolute value selects the positive distance in each interval. -/
theorem sineDistanceProduct_eq (h : ℝ) {n k : ℕ} (hk:k≤n) :
    sineDistanceProduct h n k=sineFactorial h k*sineFactorial h (n-k) := by
  -- Split at the omitted node and reverse the left distances to positive lattice indices.
  rw [sineDistanceProduct,punctured_product _ hk]
  congr 1
  · unfold sineFactorial
    rw [← prod_range_reflect (fun j => sin (((j:ℝ)+1)*h/2)) k]
    apply prod_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have hcast : ((k-1-j:ℕ):ℝ)+1=(k:ℝ)-j := by
      have he : k-1-j+1+j=k := by omega
      have her : (((k-1-j:ℕ):ℝ)+1)+(j:ℝ)=(k:ℝ) := by exact_mod_cast he
      linarith
    have hle : (j:ℝ)≤k := by exact_mod_cast (show j≤k by omega)
    rw [abs_of_nonneg (sub_nonneg.mpr hle),hcast]
  · unfold sineFactorial
    apply prod_congr rfl
    intro j _
    have hk0 := Nat.cast_nonneg k (α:=ℝ)
    have hj0 := Nat.cast_nonneg j (α:=ℝ)
    rw [Nat.cast_add,Nat.cast_add,Nat.cast_one,abs_of_nonpos (by linarith)]
    congr 1
    ring

/-- A genuine cosine gap is the positive product of its sum-angle and absolute difference-angle sines.
Use: cosine_lattice_product factors every original nonzero spectral gap without making a sign assumption on its ordering.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Source: the standard cosine subtraction formula.
Proof: the half sum lies in (0,pi). The half difference lies in (-pi,pi); in each sign case its absolute sine is the sine of its absolute argument. -/
theorem abs_cos_sub_cos {x y : ℝ} (hx:x∈Set.Ioo 0 π) (hy:y∈Set.Ioo 0 π) :
    |cos x-cos y|=2*sin ((x+y)/2)*sin (|x-y|/2) := by
  -- The sum-angle sine is positive; only the difference-angle sign depends on the node order.
  have hs : 0<sin ((x+y)/2) := sin_pos_of_pos_of_lt_pi (by linarith [hx.1,hy.1]) (by linarith [hx.2,hy.2])
  rw [cos_sub_cos,abs_mul,abs_mul,abs_of_pos hs]
  norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  by_cases hxy : y≤x
  · have hsin : 0≤sin ((x-y)/2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hx.2,hy.1])
    rw [abs_of_nonneg hsin,abs_of_nonneg (sub_nonneg.mpr hxy)]
  · have hsin : 0≤sin ((y-x)/2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hy.2,hx.1])
    rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hxy)),show (x-y)/2= -((y-x)/2) by ring,sin_neg,abs_neg,abs_of_nonneg hsin]
    congr 2
    ring

/-- The absolute cosine-lattice derivative with the omitted sum-angle factor restored has its exact complete sine-product factorization.
Use: adjacent characteristic derivatives yield the original support-weight sine ratio and its fixed-index and global estimates.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: each original gap has the preceding cosine factorization. Separate its constant, sum-angle and distance factors. Restore the single omitted sum-angle sine and evaluate both distance products exactly. -/
theorem cosine_lattice_product {h c : ℝ} {n k : ℕ} (hh:0<h) (hc:0<c)
    (hend:((n:ℝ)+c)*h<π) (hk:k≤n) :
    (∏j∈(range (n+1)).erase k,
      |cos (((k:ℝ)+c)*h)-cos (((j:ℝ)+c)*h)|)*sin ((((2*k:ℕ):ℝ)+2*c)*h/2)=
      2^n*(∏j∈range (n+1),sin (((k:ℝ)+j+2*c)*h/2))*
        sineFactorial h k*sineFactorial h (n-k) := by
  -- All original angles, including both endpoints, belong to the open half period.
  have hangle (j:ℕ) (hj:j≤n) : ((j:ℝ)+c)*h∈Set.Ioo 0 π := by
    have hj0 := Nat.cast_nonneg j (α:=ℝ)
    have hjn : (j:ℝ)≤n := by exact_mod_cast hj
    exact ⟨mul_pos (by linarith) hh,(mul_le_mul_of_nonneg_right (by linarith : (j:ℝ)+c≤(n:ℝ)+c) hh.le).trans_lt hend⟩
  have he : (∏j∈(range (n+1)).erase k,
      |cos (((k:ℝ)+c)*h)-cos (((j:ℝ)+c)*h)|)=
      2^n*(∏j∈(range (n+1)).erase k,sin (((k:ℝ)+j+2*c)*h/2))*sineDistanceProduct h n k := by
    have hcard : ((range (n+1)).erase k).card=n := by
      rw [card_erase_of_mem (mem_range.mpr (by omega)),card_range]
      omega
    have hsum (j:ℕ) : (((k:ℝ)+c)*h+((j:ℝ)+c)*h)/2=((k:ℝ)+j+2*c)*h/2 := by ring
    have hdiff (j:ℕ) : |((k:ℝ)+c)*h-((j:ℝ)+c)*h|/2=|(k:ℝ)-j| *h/2 := by
      rw [show ((k:ℝ)+c)*h-((j:ℝ)+c)*h=((k:ℝ)-j)*h by ring,abs_mul,abs_of_pos hh]
    calc
      _ = ∏j∈(range (n+1)).erase k,
          2*sin (((k:ℝ)+j+2*c)*h/2)*sin (|(k:ℝ)-j| *h/2) := by
        apply prod_congr rfl
        intro j hj
        have hjn := mem_range.mp (mem_erase.mp hj).2
        rw [abs_cos_sub_cos (hangle k hk) (hangle j (by omega)),hsum,hdiff]
      _ = _ := by simp only [prod_mul_distrib,prod_const,hcard,sineDistanceProduct]
  rw [he,sineDistanceProduct_eq h hk]
  have hp := prod_erase_mul (range (n+1)) (fun j => sin (((k:ℝ)+j+2*c)*h/2)) (mem_range.mpr (show k<n+1 by omega))
  have hmiddle : (((2*k:ℕ):ℝ)+2*c)*h/2=((k:ℝ)+(k:ℝ)+2*c)*h/2 := by push_cast; ring
  rw [hmiddle]
  calc
    _ = 2^n*((∏j∈(range (n+1)).erase k,sin (((k:ℝ)+j+2*c)*h/2))*
        sin (((k:ℝ)+(k:ℝ)+2*c)*h/2))*sineFactorial h k*sineFactorial h (n-k) := by ring
    _ = _ := by rw [hp]

end
end jacobi.Finite
