import jacobi.Comparison.PrincipalCoercivity
import jacobi.Comparison.CholeskySystem
import jacobi.Comparison.GramEntryBounds
import jacobi.Analysis.CoerciveSystem

/-!
Article: jacobi, Theorem 2.1.
The genuine original coefficient rows have uniformly bounded absolute
mass, each coefficient is uniformly O(1/N), and each actual positive
Schur normalization equals 1+O(1/N). All constants follow from the proved
actual Gram entry bounds and uniform principal-section coercivity.
Use: the continuum coefficient limit and the actual target eigenvector estimates use these same genuine rows and positive Schur normalizations.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Analysis jacobi.Finite
open scoped Topology

/-- The actual original Cholesky coefficients and normalizations satisfy
the complete uniform source size bounds on the physical half chain.
Use: the continuum coefficient limit and the actual target eigenvector
estimates use these same genuine rows and positive Schur normalizations.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: test the true preceding-Gram row system against its own solution.
The proved genuine uniform gap and finite Cauchy--Schwarz bound its total
absolute coefficient mass. Insert that bound and the original O(1/N)
Gram entries into each exact coefficient equation and the true Schur
formula; both yield one common uniform source size bound. -/
theorem cholesky_uniform_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃ K:ℝ, 0<K ∧ ∀ᶠ n:ℕ in atTop, ∀ i:Fin (n+1), 2*i.val≤n+1 →
      (∑ j:Fin i.val, |rowCoefficient a b ha hb n i j|)≤K ∧
      (∀ j:Fin i.val, ((n:ℝ)+1)*|rowCoefficient a b ha hb n i j|≤K) ∧
      ((n:ℝ)+1)*|rowNormalization a b ha hb n i-1|≤K := by
  -- Use one actual principal gap and one original Gram entry bound for every growing row.
  obtain ⟨κ,hκ,N,hgap⟩ := principalGram_uniform_coercive a b ha hb
  obtain ⟨C,hC,hentry⟩ := gramPerturbation_entry_bound ha hb
  let D : ℝ := C/κ
  let K : ℝ := D+C+C*D+1
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  filter_upwards [hentry,eventually_ge_atTop N] with n hn hN
  intro i hi
  let c := rowCoefficient a b ha hb n i
  have hbefore (j:Fin i.val) : 2*(Gram.before i j).val≤n+1 := by
    have hj := j.isLt
    change 2*j.val≤n+1
    omega
  have hne (j:Fin i.val) : i≠Gram.before i j := by
    intro he
    have hh := congrArg (fun r:Fin (n+1) => r.val) he
    have hj := j.isLt
    change i.val=j.val at hh
    omega
  have hcross (j:Fin i.val) : targetGram a b ha hb n i (Gram.before i j)=
      gramPerturbation a b ha hb n i (Gram.before i j) := by
    simp only [gramPerturbation,Matrix.sub_apply,Matrix.one_apply,hne j,ite_false,sub_zero]
  have hsys (j:Fin i.val) : (∑ k:Fin i.val, c k*
      targetGram a b ha hb n (Gram.before i k) (Gram.before i j))=
      -gramPerturbation a b ha hb n i (Gram.before i j) := by
    rw [← hcross j]
    exact rowCoefficient_system a b ha hb n i j
  have hforcing (j:Fin i.val) : |-gramPerturbation a b ha hb n i (Gram.before i j)|≤C/((n:ℝ)+1) := by
    rw [abs_neg]
    apply (le_div_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    have hh := hn i (Gram.before i j) hi (hbefore j)
    nlinarith
  -- Coercivity bounds the actual row's absolute mass without a dimension-dependent inverse constant.
  have hl1 : (∑ j:Fin i.val, |c j|)≤D := by
    apply coercive_row_l1
      (fun j k => targetGram a b ha hb n (Gram.before i j) (Gram.before i k))
      hκ hC.le (by positivity : (0:ℝ)<(n:ℝ)+1) ?_ (hgap n hN i hi) c
      (fun j => -gramPerturbation a b ha hb n i (Gram.before i j)) hsys hforcing
    simp only [Fintype.card_fin]
    have hh : (i.val:ℝ)<(n:ℝ)+1 := by exact_mod_cast i.isLt
    exact hh.le
  have hsum (j:Fin (n+1)) (hj:2*j.val≤n+1) :
      ((n:ℝ)+1)*|∑ k:Fin i.val, c k*gramPerturbation a b ha hb n (Gram.before i k) j|≤C*D := by
    exact (scaled_sum_mul_bound c
      (fun k => gramPerturbation a b ha hb n (Gram.before i k) j) (by positivity)
      (fun k => hn (Gram.before i k) j (hbefore k) hj)).trans
      (mul_le_mul_of_nonneg_left hl1 hC.le)
  -- The identity part of the true row system isolates each original coefficient.
  have hcoeff (j:Fin i.val) : ((n:ℝ)+1)*|c j|≤C+C*D := by
    have he := rowCoefficient_perturbation_system a b ha hb n i j
    have hc : c j=-(gramPerturbation a b ha hb n i (Gram.before i j)+
        ∑ k:Fin i.val, c k*gramPerturbation a b ha hb n (Gram.before i k) (Gram.before i j)) := by
      change c j+_+_=0 at he
      linarith
    rw [hc,abs_neg]
    calc
      _ ≤ ((n:ℝ)+1)*
          (|gramPerturbation a b ha hb n i (Gram.before i j)|+
            |∑ k:Fin i.val, c k*gramPerturbation a b ha hb n (Gram.before i k) (Gram.before i j)|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
      _ ≤ C+C*D := by
        rw [mul_add]
        exact add_le_add (hn i (Gram.before i j) hi (hbefore j)) (hsum (Gram.before i j) (hbefore j))
  -- The same mass estimate controls the genuine Schur complement, not a substitute normalization.
  have hq : rowNormalization a b ha hb n i-1=gramPerturbation a b ha hb n i i+
      ∑ k:Fin i.val, c k*gramPerturbation a b ha hb n (Gram.before i k) i := by
    rw [rowNormalization_formula]
    have hd : gramPerturbation a b ha hb n i i=targetGram a b ha hb n i i-1 := by
      simp only [gramPerturbation,Matrix.sub_apply,Matrix.one_apply,ite_true]
    have hx (k:Fin i.val) : targetGram a b ha hb n (Gram.before i k) i=
        gramPerturbation a b ha hb n (Gram.before i k) i := by
      simp only [gramPerturbation,Matrix.sub_apply,Matrix.one_apply,Ne.symm (hne k),ite_false,sub_zero]
    simp_rw [hx]
    rw [hd]
    dsimp [c]
    ring
  have hqbound : ((n:ℝ)+1)*|rowNormalization a b ha hb n i-1|≤C+C*D := by
    rw [hq]
    calc
      _ ≤ ((n:ℝ)+1)*
          (|gramPerturbation a b ha hb n i i|+
            |∑ k:Fin i.val, c k*gramPerturbation a b ha hb n (Gram.before i k) i|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
      _ ≤ C+C*D := by rw [mul_add]; exact add_le_add (hn i i hi hi) (hsum i hi)
  refine ⟨hl1.trans ?_,fun j => (hcoeff j).trans ?_,hqbound.trans ?_⟩ <;>
    dsimp [K] <;> nlinarith [mul_nonneg hC.le hD.le]

end
end jacobi.Comparison
