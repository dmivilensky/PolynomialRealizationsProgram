import jacobi.Counterexample.LaguerreFactor
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
Article: jacobi, Proposition 6.1.
Gershgorin's theorem is applied to the actual swapped Cholesky matrix.
Its spectrum is exactly that of the original Laguerre recurrence matrix.
Bounding each adjacent product by half the sum of its two squares gives
the printed upper bound throughout a>-1, including dimension one.
Source: Gershgorin's circle theorem; Szego, Orthogonal Polynomials,
the Laguerre recurrence matrix.
Use: laguerre_swapped_row_bound controls both neighboring entries, including the first row where the original unswapped arithmetic-mean bound needs a separate case.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Each true adjacent product of the swapped Laguerre factor has an elementary arithmetic-mean bound.
Use: laguerre_swapped_row_bound controls both neighboring entries, including the first row where the original unswapped arithmetic-mean bound needs a separate case.
Article: jacobi, Section 6 (bidiagonal swap identity).
Source: the arithmetic-geometric mean inequality for two real squares.
Proof: the actual two square-root squares are i+a+1 and i; their squared difference is nonnegative. -/
theorem laguerre_product_bound {a:ℝ} (ha:-1<a) (i:ℕ) :
    laguerreLower i*laguerreDiagonal a i≤(i:ℝ)+(a+1)/2 := by
  have h := two_mul_le_add_sq (laguerreLower i) (laguerreDiagonal a i)
  rw [laguerreLower,laguerreDiagonal,Real.sq_sqrt (Nat.cast_nonneg i),
    Real.sq_sqrt (by linarith [Nat.cast_nonneg (α:=ℝ) i])] at h
  unfold laguerreLower laguerreDiagonal
  linarith

/-- A single physical neighboring index contributes at most its nonnegative bound to a finite row sum.
Use: laguerre_swapped_row_bound sums the two possible adjacent entries without adding a nonexistent boundary index.
Article: jacobi, Proposition 6.1.
Proof: if the predicate holds anywhere, its uniqueness reduces the sum to that one term; otherwise every summand is zero. -/
private theorem singleton_sum_bound {N:ℕ} (p:Fin N→Prop) [DecidablePred p]
    (hp:∀i j,p i→p j→i=j) {A:ℝ} (hA:0≤A) :
    (∑j:Fin N,if p j then A else 0)≤A := by
  classical
  by_cases he:∃j,p j
  · obtain ⟨j,hj⟩ := he
    have heq (i:Fin N) : p i ↔ i=j := ⟨fun hi=>hp i j hi hj,fun hi=>hi.symm ▸ hj⟩
    simp only [heq,Finset.sum_ite_eq',Finset.mem_univ,ite_true,le_refl]
  · have hn (j:Fin N) : ¬p j := fun hj=>he ⟨j,hj⟩
    simpa only [hn,ite_false,Finset.sum_const_zero] using hA

/-- Every full absolute row sum of the actual swapped Laguerre matrix is at most 4*i+2*a+4.
Use: laguerre_spectrum_upper obtains a strict spectral bound with no unproved eigenvalue or polynomial hypothesis.
Article: jacobi, Proposition 6.1.
Proof: bound its diagonal by 2*i+a+2 and its two adjacent products
by i+(a+1)/2 and i+1+(a+1)/2. The exact finite matrix entry formula
and singleton sums retain both missing-boundary conventions. -/
theorem laguerre_swapped_row_bound {N:ℕ} {a:ℝ} (ha:-1<a) (i:Fin N) :
    (∑j:Fin N,‖swappedGram (laguerreDiagonal a) laguerreLower N i j‖)≤
      4*(i:ℝ)+2*a+4 := by
  classical
  -- The row estimate concerns the literal Cholesky swap, before taking its unchanged spectrum.
  let A:ℝ := 2*(i:ℝ)+a+2
  let L:ℝ := (i:ℝ)+(a+1)/2
  let R:ℝ := (i:ℝ)+1+(a+1)/2
  have hA:0≤A := by dsimp [A]; linarith [Nat.cast_nonneg (α:=ℝ) i.val]
  have hL:0≤L := by dsimp [L]; linarith [Nat.cast_nonneg (α:=ℝ) i.val]
  have hR:0≤R := by dsimp [R]; linarith [Nat.cast_nonneg (α:=ℝ) i.val]
  have hentry (j:Fin N) :
      ‖swappedGram (laguerreDiagonal a) laguerreLower N i j‖≤
        (if i=j then A else 0)+(if j.val+1=i.val then L else 0)+
          (if i.val+1=j.val then R else 0) := by
    rw [swapped_entry]
    by_cases hij:i=j
    · subst j
      have hn:¬i.val+1=i.val := by omega
      simp only [ite_true,hn,ite_false,add_zero,Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      rw [laguerreDiagonal,Real.sq_sqrt (by linarith [Nat.cast_nonneg (α:=ℝ) i.val])]
      split_ifs with hi
      · rw [laguerreLower,Real.sq_sqrt (Nat.cast_nonneg (i.val+1))]
        push_cast
        dsimp only [A]
        linarith
      · dsimp only [A]
        linarith [Nat.cast_nonneg (α:=ℝ) i.val]
    · by_cases hu:i.val+1=j.val
      · have hl:¬j.val+1=i.val := by omega
        simp only [hij,ite_false,hu,ite_true,hl,zero_add,add_zero,Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (show 0≤laguerreLower j from Real.sqrt_nonneg _)
          (laguerreDiagonal_pos ha j).le)]
        have hh := laguerre_product_bound ha j.val
        have hc:(j:ℝ)=(i:ℝ)+1 := by exact_mod_cast hu.symm
        simpa only [R,hc] using hh
      · by_cases hl:j.val+1=i.val
        · simp only [hij,ite_false,hu,hl,ite_true,zero_add,add_zero,Real.norm_eq_abs]
          rw [abs_of_nonneg (mul_nonneg (laguerreDiagonal_pos ha i).le
            (show 0≤laguerreLower i from Real.sqrt_nonneg _))]
          simpa only [L,mul_comm] using laguerre_product_bound ha i.val
        · simp only [hij,ite_false,hu,hl,zero_add,norm_zero,le_refl]
  have hleft := singleton_sum_bound (fun j:Fin N=>j.val+1=i.val)
    (fun j k hj hk=>Fin.ext (by omega)) hL
  have hright := singleton_sum_bound (fun j:Fin N=>i.val+1=j.val)
    (fun j k hj hk=>Fin.ext (by omega)) hR
  calc
    _ ≤ ∑j:Fin N,((if i=j then A else 0)+(if j.val+1=i.val then L else 0)+
        (if i.val+1=j.val then R else 0)) := Finset.sum_le_sum fun j _=>hentry j
    _ = A+(∑j:Fin N,if j.val+1=i.val then L else 0)+
        (∑j:Fin N,if i.val+1=j.val then R else 0) := by simp only [Finset.sum_add_distrib]; simp
    _ ≤ A+L+R := by linarith
    _ = _ := by dsimp [A,L,R]; ring

/-- Every eigenvalue of the original Laguerre matrix obeys the source's strict upper bound for every a>-1.
Use: laguerre_counterexample_admissible discharges the complete spectral-window premise for the actual counterexample attaining chain.
Article: jacobi, Section 6 (bidiagonal swap identity).
Source: the community Gershgorin theorem, applied after the exact Cholesky swap.
Proof: the unchanged complete characteristic polynomial transfers
the actual spectral value to the swap. Gershgorin and the full absolute
row estimate give y<=4*i+2*a+4<=4*n+2*a, hence the printed strict bound. -/
theorem laguerre_spectrum_upper {N:ℕ} {a y:ℝ} (ha:-1<a)
    (hy:y∈spectrum ℝ (bidiagonal (laguerreDiagonal a) laguerreLower N*
      (bidiagonal (laguerreDiagonal a) laguerreLower N)ᵀ)) :
    y<4*(N:ℝ)+2*a+2 := by
  classical
  -- No root-location assumption is supplied: the spectral value is that of the genuine original matrix.
  let Y := swappedGram (laguerreDiagonal a) laguerreLower N
  have hswap:y∈spectrum ℝ Y := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly,swapped_charpoly]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hy
  have heig:Module.End.HasEigenvalue (Matrix.toLin' Y) y :=
    Module.End.HasEigenvalue.of_mem_spectrum (by simpa only [Matrix.spectrum_toLin'] using hswap)
  obtain ⟨i,hi⟩ := eigenvalue_mem_ball heig
  have hi' : y≤Y i i+∑j∈Finset.univ.erase i,‖Y i j‖ := by
    rw [Metric.mem_closedBall,Real.dist_eq] at hi
    linarith [(le_abs_self (y-Y i i)).trans hi]
  have hdiag:0≤Y i i := by
    change 0≤swappedGram (laguerreDiagonal a) laguerreLower N i i
    rw [swapped_entry,ite_eq_left rfl]
    positivity
  have hsum:Y i i+∑j∈Finset.univ.erase i,‖Y i j‖=∑j:Fin N,‖Y i j‖ := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i),Real.norm_eq_abs,abs_of_nonneg hdiag]
    ring
  rw [hsum] at hi'
  have hb := hi'.trans (laguerre_swapped_row_bound ha i)
  have hn:(i:ℝ)+1≤N := by exact_mod_cast i.isLt
  linarith

end
end jacobi.Counterexample
