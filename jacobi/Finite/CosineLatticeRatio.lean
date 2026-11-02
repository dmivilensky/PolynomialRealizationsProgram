import jacobi.Finite.CosineLatticeProducts

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Adjacent original characteristic-gap products have an exact six-sine
ratio. All cancellations are justified by the open physical angle range.
This ratio will be applied to the canonical support spectral measure.
Use: naturalMeasure_adjacent_ratio inserts the true truncation period and obtains the printed sine-cosine ratio of the actual support probabilities.
-/
namespace jacobi.Finite
noncomputable section
open Real Finset

/-- The adjacent absolute characteristic derivatives on a cosine lattice have the exact original telescoping ratio.
Use: naturalMeasure_adjacent_ratio inserts the true truncation period and obtains the printed sine-cosine ratio of the actual support probabilities.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: use the complete sine factorization for each derivative. The sum-angle window slides by one, one distance factorial gains a factor and the other loses one. Every cancelled sine and finite product is positive. -/
theorem cosine_lattice_derivative_ratio {h c : ℝ} {n k : ℕ}
    (hh:0<h) (hc:0<c) (hend:((n:ℝ)+c)*h<π) (hk:k<n) :
    (∏j∈(range (n+1)).erase k,
      |cos (((k:ℝ)+c)*h)-cos (((j:ℝ)+c)*h)|)/
      (∏j∈(range (n+1)).erase (k+1),
        |cos ((((k+1:ℕ):ℝ)+c)*h)-cos (((j:ℝ)+c)*h)|)=
      sin (((k:ℝ)+2*c)*h/2)*sin (((n:ℝ)-k)*h/2)*sin (((k:ℝ)+1+c)*h)/
        (sin (((k:ℝ)+n+1+2*c)*h/2)*sin (((k:ℝ)+1)*h/2)*sin (((k:ℝ)+c)*h)) := by
  -- Positive endpoint angles justify all finite products, including the empty ones.
  let S (m:ℕ) := ∏j∈range (n+1),sin (((m:ℝ)+j+2*c)*h/2)
  let F := sineFactorial h
  have hsin (x:ℝ) (hx:0<x) (hxn:x≤(n:ℝ)+c) : 0<sin (x*h) :=
    sin_pos_of_pos_of_lt_pi (mul_pos hx hh)
      ((mul_le_mul_of_nonneg_right hxn hh.le).trans_lt hend)
  have hF (m:ℕ) (hm:m≤n) : F m≠0 := by
    apply ne_of_gt
    apply prod_pos
    intro j hj
    have hjn : (j:ℝ)+1≤n := by exact_mod_cast (show j+1≤n by have := mem_range.mp hj; omega)
    have hj0 := Nat.cast_nonneg j (α:=ℝ)
    have hp : 0<sin ((((j:ℝ)+1)/2)*h) := hsin _ (by linarith) (by linarith)
    convert hp using 1
    congr 1
    ring
  have hS (m:ℕ) (hm:m≤n) : S m≠0 := by
    apply ne_of_gt
    apply prod_pos
    intro j hj
    have hjn : (j:ℝ)≤n := by exact_mod_cast (show j≤n by have := mem_range.mp hj; omega)
    have hmn : (m:ℝ)≤n := by exact_mod_cast hm
    have hj0 := Nat.cast_nonneg j (α:=ℝ)
    have hm0 := Nat.cast_nonneg m (α:=ℝ)
    have hp : 0<sin ((((m:ℝ)+j+2*c)/2)*h) := hsin _ (by linarith) (by linarith)
    convert hp using 1
    congr 1
    ring
  have hkr : (k:ℝ)+1≤n := by exact_mod_cast hk
  have hk0 := Nat.cast_nonneg k (α:=ℝ)
  have hs₀ : sin (((k:ℝ)+c)*h)≠0 := ne_of_gt (hsin _ (by linarith) (by linarith))
  have hs₁ : sin (((k:ℝ)+1+c)*h)≠0 := ne_of_gt (hsin _ (by linarith) (by linarith))
  have hp₀ : sin (((k:ℝ)+2*c)*h/2)≠0 := by
    have hp := hsin (((k:ℝ)+2*c)/2) (by linarith) (by linarith)
    convert ne_of_gt hp using 1
    congr 2
    ring
  have hp₁ : sin (((k:ℝ)+n+1+2*c)*h/2)≠0 := by
    have hp := hsin (((k:ℝ)+n+1+2*c)/2) (by linarith) (by linarith)
    convert ne_of_gt hp using 1
    congr 2
    ring
  have hd₀ : sin (((k:ℝ)+1)*h/2)≠0 := by
    have hp := hsin (((k:ℝ)+1)/2) (by linarith) (by linarith)
    convert ne_of_gt hp using 1
    congr 2
    ring
  have hd₁ : sin (((n:ℝ)-k)*h/2)≠0 := by
    have hp := hsin (((n:ℝ)-k)/2) (by linarith) (by linarith)
    convert ne_of_gt hp using 1
    congr 2
    ring
  -- The window and both factorials telescope before any quotient is simplified.
  have hslide : S (k+1)=S k*sin (((k:ℝ)+n+1+2*c)*h/2)/sin (((k:ℝ)+2*c)*h/2) := by
    apply (eq_div_iff hp₀).mpr
    convert sliding_product (fun j => sin (((j:ℝ)+2*c)*h/2)) n k using 1 <;>
      simp only [S,Nat.cast_add,Nat.cast_one]
  have hnext : F (k+1)=F k*sin (((k:ℝ)+1)*h/2) := prod_range_succ _ _
  have hprev : F (n-k)=F (n-(k+1))*sin (((n:ℝ)-k)*h/2) := by
    have he : n-k=(n-(k+1))+1 := by omega
    rw [he]
    change sineFactorial h (n-(k+1)+1)=_
    rw [sineFactorial,prod_range_succ]
    have hcast : ((n-(k+1):ℕ):ℝ)+1=(n:ℝ)-k := by
      have hnc : ((n-(k+1):ℕ):ℝ)+(k:ℝ)+1=n := by exact_mod_cast (show n-(k+1)+k+1=n by omega)
      linarith
    rw [hcast]
    rfl
  have h₀ := cosine_lattice_product hh hc hend hk.le
  have h₁ := cosine_lattice_product hh hc hend (show k+1≤n by omega)
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] at h₀ h₁
  have hm₀ : (2*(k:ℝ)+2*c)*h/2=((k:ℝ)+c)*h := by ring
  have hm₁ : (2*((k:ℝ)+1)+2*c)*h/2=((k:ℝ)+1+c)*h := by ring
  rw [hm₀] at h₀
  rw [hm₁] at h₁
  have h₁' : (∏j∈(range (n+1)).erase (k+1),
      |cos (((k:ℝ)+1+c)*h)-cos (((j:ℝ)+c)*h)|)=
        2^n*S (k+1)*F (k+1)*F (n-(k+1))/sin (((k:ℝ)+1+c)*h) := by
    simpa only [S,F,Nat.cast_add,Nat.cast_one] using (eq_div_iff hs₁).mpr h₁
  simp only [Nat.cast_add,Nat.cast_one]
  rw [(eq_div_iff hs₀).mpr h₀,h₁']
  change (2^n*S k*F k*F (n-k)/sin (((k:ℝ)+c)*h))/
    (2^n*S (k+1)*F (k+1)*F (n-(k+1))/sin (((k:ℝ)+1+c)*h))=_
  rw [hslide,hnext,hprev]
  field_simp [hs₀,hs₁,hp₀,hp₁,hd₀,hd₁,hS k hk.le,hF k hk.le,hF (n-(k+1)) (by omega)]

end
end jacobi.Finite
