import jacobi.Jacobi.Nodes
import jacobi.Jacobi.EndpointDerivatives

/-!
Article: jacobi, Theorem 5.1.
The actual complete finite Jacobi zero list gives the genuine polynomial
logarithmic derivative. Differentiating it evaluates both finite inverse
root sums from the already proved actual endpoint derivatives.
Source: Polynomial.Splits.eval_derivative_div_eval_of_ne_zero and genuine finite-sum differentiation.
Use: converts community polynomial root formulas into the article's canonical finite index sums.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The canonical sorted zero enumeration reproduces the original full root multiset, with no lost multiplicities.
Use: converts community polynomial root formulas into the article's canonical finite index sums.
Article: jacobi, Lemma 1.3.
Proof: the community finite order embedding maps the full finite index
set onto the actual root finset, whose multiset is the original duplicate-free root multiset. -/
theorem shiftedRoots_multiset {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    ((Finset.univ:Finset (Fin n)).val.map (shiftedRoots a b ha hb n))=
      (shiftedPolynomial a b n).roots := by
  classical
  have h := congrArg Finset.val (Finset.map_orderEmbOfFin_univ
    (shiftedPolynomial a b n).roots.toFinset
    ((Multiset.toFinset_card_of_nodup (shiftedPolynomial_roots ha hb n).2.1).trans
      (shiftedPolynomial_roots ha hb n).1))
  simpa only [Finset.map_val,RelEmbedding.coe_toEmbedding,Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (shiftedPolynomial_roots ha hb n).2.1,shiftedRoots] using h

/-- A sum over the complete actual root multiset equals the canonical finite Jacobi index sum.
Use: translates logarithmic derivatives and finite Rayleigh sums without a separate spectral list.
Article: jacobi, Lemma 1.3.
Proof: map the literal summand through the proved exact root multiset enumeration. -/
theorem shiftedRoots_sum {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) (f : ℝ → ℝ) :
    ((shiftedPolynomial a b n).roots.map f).sum=∑ i:Fin n,f (shiftedRoots a b ha hb n i) := by
  have h := congrArg (fun s : Multiset ℝ => (s.map f).sum) (shiftedRoots_multiset ha hb n)
  simpa only [Multiset.map_map,Function.comp_def,Finset.sum] using h.symm

/-- The actual Jacobi logarithmic derivative is the sum over its complete canonically ordered finite zeros.
Use: evaluates both finite inverse-root moments and the scaled resolvent traces.
Article: jacobi, Lemma 1.3.
Proof: apply the community splitting theorem to the actual polynomial,
then use its proved exact root enumeration. -/
theorem shifted_logarithmic_derivative {a b : ℝ} (ha : -1<a) (hb : -1<b)
    (n : ℕ) {x : ℝ} (hx : (shiftedPolynomial a b n).eval x≠0) :
    (shiftedPolynomial a b n).derivative.eval x/(shiftedPolynomial a b n).eval x=
      ∑ i:Fin n,1/(x-shiftedRoots a b ha hb n i) := by
  rw [(shiftedPolynomial_roots ha hb n).2.2.2.eval_derivative_div_eval_of_ne_zero hx,
    shiftedRoots_sum ha hb]

/-- The actual finite shifted Jacobi inverse-root sum has its exact closed formula.
Use: proves the finite edge mass and its genuine limiting value.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: evaluate the genuine logarithmic derivative at zero. The actual
endpoint value is one and its exact first derivative is already proved. -/
theorem shifted_inverse_root_sum {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (∑ i:Fin n,1/shiftedRoots a b ha hb n i)=(n:ℝ)*(n+a+b+1)/(a+1) := by
  have h := shifted_logarithmic_derivative ha hb n (x := 0) (by rw [shiftedPolynomial_zero]; norm_num)
  rw [shiftedPolynomial_zero,shiftedPolynomial_derivative_zero ha] at h
  simp only [div_one,zero_sub,one_div_neg_eq_neg_one_div,Finset.sum_neg_distrib] at h
  simpa only [neg_mul,neg_div,neg_inj] using h.symm

/-- The second inverse-root sum is the square of the first endpoint logarithmic derivative minus the true second derivative.
Use: evaluates the actual finite second Rayleigh sum from the original polynomial.
Article: jacobi, Lemma 1.3.
Proof: differentiate the actual finite logarithmic derivative near the
nonzero endpoint. Its quotient derivative is p''(0)-p'(0)^2, while the
genuine finite reciprocal sum has derivative minus the sum of squared
reciprocals. Uniqueness of ordinary derivatives identifies them. -/
theorem shifted_inverse_root_square_sum {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (∑ i:Fin n,(1/shiftedRoots a b ha hb n i)^2)=
      ((shiftedPolynomial a b n).derivative.eval 0)^2-
        (shiftedPolynomial a b n).derivative.derivative.eval 0 := by
  -- The neighborhood identity differentiates actual finite functions; no formal logarithm is substituted.
  let p := shiftedPolynomial a b n
  have hp0 : p.eval 0≠0 := by rw [shiftedPolynomial_zero]; norm_num
  have hL := (p.derivative.hasDerivAt 0).div (p.hasDerivAt 0) hp0
  have hE : (fun x : ℝ => p.derivative.eval x/p.eval x)=ᶠ[𝓝 0]
      (fun x : ℝ => ∑ i:Fin n,1/(x-shiftedRoots a b ha hb n i)) := by
    filter_upwards [p.continuous.continuousAt.eventually_ne hp0] with x hx
    exact shifted_logarithmic_derivative ha hb n hx
  have hR (i : Fin n) : HasDerivAt (fun x : ℝ => 1/(x-shiftedRoots a b ha hb n i))
      (-(1/shiftedRoots a b ha hb n i)^2) 0 := by
    have hi : (0:ℝ)-shiftedRoots a b ha hb n i≠0 :=
      sub_ne_zero.mpr (ne_of_lt (shiftedRoots_properties ha hb i).2.1)
    convert ((hasDerivAt_id (0:ℝ)).sub_const (shiftedRoots a b ha hb n i)).inv hi using 1
    · ext x
      simp only [one_div,id_eq,Pi.inv_apply]
    · simp only [id_eq,zero_sub,neg_sq,div_pow,one_pow,neg_div]
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hR i)
  have he := (hL.congr_of_eventuallyEq hE.symm).unique hsum
  rw [shiftedPolynomial_zero] at he
  simp only [one_pow,mul_one,div_one,Finset.sum_neg_distrib] at he
  linarith

end
end jacobi.Jacobi
