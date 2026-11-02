import jacobi.Finite.FlowPolynomialMinimum
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
Dominant-atom limits of the actual monic polynomials in a finite flow.
The square-norm minimum compares a leading continuant with the polynomial
vanishing on the earlier dominant atoms. Every remaining weight ratio
tends to zero. Lagrange interpolation then determines the subleading
coefficient, and hence the physical prefix trace used in matrix sorting.
Use: FlowSorting applies these estimates to both resolvent time directions.
Article: jacobi, Proposition 5.5 and Section 5.6.
Article role: both sorted matrix limits, limiting Richardson energy and its quartic Jacobi
asymptotic.
-/
namespace jacobi.Finite
noncomputable section
open Real Polynomial Filter Set chebyshev1 chebyshev2
open scoped Topology BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/-- The monic polynomial vanishing at the first m atoms in the chosen
dominance order. It is the comparison polynomial for the norm minimum.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
def dominancePolynomial {N : ℕ} (x : Fin N → ℝ) (ord : Fin N ≃ Fin N)
    (m : ℕ) (hm : m≤N) : ℝ[X] :=
  ∏ j : Fin m,(X-C (x (ord ⟨j.val,j.isLt.trans_le hm⟩)))

/-- The comparison polynomial is genuinely monic of exactly degree m.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem dominancePolynomial_degree {N : ℕ} (x : Fin N → ℝ) (ord : Fin N ≃ Fin N)
    (m : ℕ) (hm : m≤N) : (dominancePolynomial x ord m hm).IsMonicOfDegree m := by
  constructor
  · rw [dominancePolynomial,natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
    simp
  · exact monic_prod_X_sub_C _ _

/-- All earlier dominant atoms are exact zeros of the comparison
polynomial, independently of the time-dependent measure.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem dominancePolynomial_zero {N : ℕ} (x : Fin N → ℝ) (ord : Fin N ≃ Fin N)
    {m : ℕ} (hm : m≤N) (j : Fin N) (hj : j.val < m) :
    (dominancePolynomial x ord m hm).eval (x (ord j))=0 := by
  simp only [dominancePolynomial,eval_prod,eval_sub,eval_X,eval_C]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨j.val,hj⟩ : Fin m))
  simp

/-- The norm minimum forces every actual leading polynomial to vanish
asymptotically at the earlier dominant atoms. This is the essential sorting
estimate; the full matrix limit is subsequently obtained from prefix traces.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem leading_dominant_atom_limit {N : ℕ} (M : ℝ → DiscreteMeasure N)
    (x : Fin N → ℝ) (hx : ∀ t,(M t).node=x) (ord : Fin N ≃ Fin N)
    (hratio : ∀ j k : Fin N,j < k →
      Tendsto (fun t : ℝ => (M t).weight (ord k)/(M t).weight (ord j)) atTop (𝓝 0))
    (i j : Fin N) (hji : j < i) :
    Tendsto (fun t : ℝ => ((M t).reconstructed.data.leading i).eval (x (ord j)))
      atTop (𝓝 0) := by
  let q := dominancePolynomial x ord i.val i.isLt.le
  have hq := dominancePolynomial_degree x ord i.val i.isLt.le
  have hmajor : Tendsto (fun t : ℝ => (M t).polynomialSquareNorm q/(M t).weight (ord j))
      atTop (𝓝 0) := by
    have he (t : ℝ) : (M t).polynomialSquareNorm q/(M t).weight (ord j)=
        ∑ k : Fin N,((M t).weight (ord k)/(M t).weight (ord j))*(q.eval (x (ord k)))^2 := by
      rw [DiscreteMeasure.polynomialSquareNorm,← Equiv.sum_comp ord,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      rw [hx]
      ring
    simp_rw [he]
    have h (k : Fin N) : Tendsto (fun t : ℝ =>
        ((M t).weight (ord k)/(M t).weight (ord j))*(q.eval (x (ord k)))^2) atTop (𝓝 0) := by
      by_cases hki : k.val < i.val
      · have hz : q.eval (x (ord k))=0 := dominancePolynomial_zero x ord i.isLt.le k hki
        simp only [hz,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]
        exact tendsto_const_nhds
      · have h := (hratio j k (by change j.val < k.val; omega)).mul_const ((q.eval (x (ord k)))^2)
        simpa only [zero_mul] using h
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun k _ => h k)
  have hs : Tendsto (fun t : ℝ => (((M t).reconstructed.data.leading i).eval (x (ord j)))^2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _ hmajor
    intro t
    have hp := (M t).positive (ord j)
    have hsingle : (M t).weight (ord j)*
        (((M t).reconstructed.data.leading i).eval (x (ord j)))^2≤
        (M t).polynomialSquareNorm ((M t).reconstructed.data.leading i) := by
      rw [DiscreteMeasure.polynomialSquareNorm]
      rw [← hx t]
      exact Finset.single_le_sum (f := fun k => (M t).weight k*
        (((M t).reconstructed.data.leading i).eval ((M t).node k))^2)
        (fun k _ => mul_nonneg ((M t).positive k).le (sq_nonneg _))
        (Finset.mem_univ (ord j))
    apply (le_div_iff₀ hp).mpr
    rw [mul_comm]
    exact hsingle.trans ((M t).leading_minimum i hq.monic hq.natDegree_eq)
  have h := hs.sqrt
  simp only [sqrt_zero,sqrt_sq_eq_abs] at h
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using h)

/-- The subleading coefficient of the actual monic continuant converges
to that of the dominant-atom product. Interpolation uses exactly i distinct
atoms, and every value in its finite sum has already been controlled.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem leading_subleading_limit {N : ℕ} (M : ℝ → DiscreteMeasure N)
    (x : Fin N → ℝ) (hx : ∀ t,(M t).node=x) (ord : Fin N ≃ Fin N)
    (hratio : ∀ j k : Fin N,j < k →
      Tendsto (fun t : ℝ => (M t).weight (ord k)/(M t).weight (ord j)) atTop (𝓝 0))
    (i : Fin N) (hi : 0 < i.val) :
    Tendsto (fun t : ℝ => ((M t).reconstructed.data.leading i).coeff (i.val-1)) atTop
      (𝓝 (-(∑ j : Fin i.val,x (ord ⟨j.val,j.isLt.trans i.isLt⟩)))) := by
  let q := dominancePolynomial x ord i.val i.isLt.le
  let v : Fin i.val → ℝ := fun j => x (ord ⟨j.val,j.isLt.trans i.isLt⟩)
  have hv : Function.Injective v := by
    intro j k h
    have hxinj : Function.Injective x := by rw [← hx 0]; exact (M 0).distinct
    have h := ord.injective (hxinj h)
    exact Fin.ext (congrArg (fun z : Fin N => z.val) h)
  have hq := dominancePolynomial_degree x ord i.val i.isLt.le
  have hrepr (t : ℝ) :
      (((M t).reconstructed.data.leading i)-q).coeff (i.val-1)=
        ∑ j : Fin i.val,((M t).reconstructed.data.leading i).eval (v j)/
          ∏ k∈Finset.univ.erase j,(v j-v k) := by
    have hp : ((M t).reconstructed.data.leading i).IsMonicOfDegree i.val :=
      ⟨(M t).reconstructed.data.block_natDegree (M t).reconstructed.coupling_nonneg 0 i,
        (M t).reconstructed.data.block_monic (M t).reconstructed.coupling_nonneg 0 i⟩
    have hd := hp.natDegree_sub_lt hi.ne' hq
    have hd' : (((M t).reconstructed.data.leading i)-q).degree<(i.val:ℕ) := by
      by_cases hz : ((M t).reconstructed.data.leading i)-q=0
      · rw [hz,degree_zero]
        exact WithBot.bot_lt_coe _
      · exact (natDegree_lt_iff_degree_lt hz).mp hd
    have h := Lagrange.coeff_eq_sum (s := Finset.univ) (v := v) hv.injOn
      (by simpa only [Finset.card_univ,Fintype.card_fin] using hd')
    simp only [Finset.card_univ,Fintype.card_fin,eval_sub] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro j _
    have hz : q.eval (v j)=0 := dominancePolynomial_zero x ord i.isLt.le
      ⟨j.val,j.isLt.trans i.isLt⟩ j.isLt
    rw [hz,sub_zero]
  have hdiff : Tendsto (fun t : ℝ =>
      (((M t).reconstructed.data.leading i)-q).coeff (i.val-1)) atTop (𝓝 0) := by
    simp_rw [hrepr]
    have h := tendsto_finsetSum Finset.univ (fun j _ =>
      (leading_dominant_atom_limit M x hx ord hratio i
        ⟨j.val,j.isLt.trans i.isLt⟩ j.isLt).div_const
          (∏ k∈Finset.univ.erase j,(v j-v k)))
    simpa only [zero_div,Finset.sum_const_zero] using h
  have hqc : q.coeff (i.val-1)= -∑ j : Fin i.val,v j := by
    have hs : (Finset.univ : Finset (Fin i.val)).Nonempty :=
      ⟨⟨0,hi⟩,Finset.mem_univ _⟩
    simpa only [q,dominancePolynomial,Finset.card_univ,Fintype.card_fin] using
      prod_X_sub_C_coeff_card_pred _ _ hs.card_pos
  have h := hdiff.add_const (q.coeff (i.val-1))
  simpa only [coeff_sub,sub_add_cancel,zero_add,hqc] using h

end
end jacobi.Finite
