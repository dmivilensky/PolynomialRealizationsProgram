import jacobi.Jacobi.Orthogonality
import jacobi.Jacobi.RootFactor
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Splits

/-!
Article: jacobi, Proposition A.1.
Full lower-degree orthogonality forces all roots into (0,1), with no
complex roots or repeated roots left over. The proof uses the actual
Jacobi weight and proves the generic orthogonal-polynomial fact explicitly.
Source: the classical zero theorem for real orthogonal polynomials.
Use: proves completeness of the finite Jacobi zero list and excludes every nonreal or exterior root.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- Lower-degree Jacobi-weight orthogonality forces a nonzero real polynomial to have its full degree of roots, all inside the open unit interval.
Use: proves completeness of the finite Jacobi zero list and excludes every nonreal or exterior root.
Article: jacobi, Proposition A.1.
Proof: factor out all interior real roots with multiplicity. If that
factor had lower degree, orthogonality would make its pairing zero,
while the zero-free remaining factor gives the proved nonzero pairing.
Hence the interior root factor already has full degree. -/
theorem roots_of_orthogonality {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {p : Polynomial ℝ} (hp : p≠0)
    (ho : ∀ q : Polynomial ℝ,q.natDegree<p.natDegree →
      (∫ t in (0:ℝ)..1,weight a b t*(p.eval t*q.eval t))=0) :
    p.roots.card=p.natDegree ∧ ∀ t∈p.roots,t∈Ioo (0:ℝ) 1 := by
  classical
  -- The root factor contains every interior multiplicity, and its remainder cannot change sign.
  obtain ⟨q,r,he,hq,hr,hqcard,hrzero⟩ := factor_interior_roots hp
  have hdeg : p.natDegree=q.natDegree+r.natDegree := by rw [he,natDegree_mul hq hr]
  have hqeq : q.natDegree=p.natDegree := by
    apply le_antisymm (by omega)
    by_contra hn
    have hlt : q.natDegree<p.natDegree := lt_of_not_ge hn
    exact root_factor_pairing_ne_zero ha hb hp hq he hrzero (ho q hlt)
  have hfiltercard := Multiset.card_le_card (Multiset.filter_le (fun t => t∈Ioo (0:ℝ) 1) p.roots)
  have hcard : p.roots.card=p.natDegree := by
    apply le_antisymm (card_roots' p)
    rw [← hqeq,hqcard]
    exact hfiltercard
  have hfilter : p.roots.filter (fun t => t∈Ioo (0:ℝ) 1)=p.roots :=
    Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _) (by rw [← hqcard,hqeq,hcard])
  refine ⟨hcard,?_⟩
  intro t ht
  have hmem : t∈p.roots.filter (fun t => t∈Ioo (0:ℝ) 1) := by rwa [hfilter]
  exact (Multiset.mem_filter.mp hmem).2

/-- Lower-degree Jacobi-weight orthogonality excludes every repeated real root.
Use: supplies genuine simplicity and a duplicate-free canonical finite zero ordering.
Article: jacobi, Proposition A.1.
Proof: a repeated root would give p=(X-c)^2*q with q of lower degree.
Then p*q=(X-c)^2*q^2 is a nonzero nonnegative polynomial, whose genuine
weighted integral is positive, contradicting orthogonality to q. -/
theorem simple_roots_of_orthogonality {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {p : Polynomial ℝ} (hp : p≠0)
    (ho : ∀ q : Polynomial ℝ,q.natDegree<p.natDegree →
      (∫ t in (0:ℝ)..1,weight a b t*(p.eval t*q.eval t))=0) (c : ℝ) :
    p.rootMultiplicity c≤1 := by
  -- Retain the actual square factor; positivity then needs no ODE uniqueness assumption.
  by_contra hn
  have hmult : 2≤p.rootMultiplicity c := by omega
  have hdiv : (X-C c)^2∣p := (le_rootMultiplicity_iff hp).mp hmult
  obtain ⟨q,he⟩ := hdiv
  have hfac : ((X-C c)^2:Polynomial ℝ)≠0 := pow_ne_zero _ (X_sub_C_ne_zero c)
  have hq : q≠0 := right_ne_zero_of_mul (he ▸ hp)
  have hdeg : p.natDegree=2+q.natDegree := by
    rw [he,natDegree_mul hfac hq,natDegree_pow,natDegree_X_sub_C]
  have hqdeg : q.natDegree<p.natDegree := by omega
  have hnon : ∀ t∈Ioo (0:ℝ) 1,0≤(p*q).eval t := by
    intro t _
    have hv : (p*q).eval t=(t-c)^2*(q.eval t)^2 := by
      rw [he]
      simp only [eval_mul,eval_pow,eval_sub,eval_X,eval_C]
      ring
    rw [hv]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpos := weighted_polynomial_integral_pos ha hb (mul_ne_zero hp hq) hnon
  simp only [eval_mul] at hpos
  rw [ho q hqdeg] at hpos
  exact lt_irrefl _ hpos

/-- The actual shifted Jacobi polynomial has exactly n simple roots, all strictly inside (0,1), and splits over the reals.
Use: the article's full finite zero list, finite factorization, spectral trace formulas and ordered Mehler--Heine transfer.
Article: jacobi, Proposition A.1.
Proof: apply the proved generic orthogonal-polynomial root theorems
to the actual degree-n Jacobi polynomial and its complete genuine
lower-degree orthogonality. Root multiplicity at most one gives the
duplicate-free multiset, and the full root count gives real splitting. -/
theorem shiftedPolynomial_roots {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    let p := shiftedPolynomial a b n
    p.roots.card=n ∧ p.roots.Nodup ∧ (∀ t∈p.roots,t∈Ioo (0:ℝ) 1) ∧ p.Splits := by
  classical
  -- All hypotheses are discharged for the actual original Jacobi family.
  let p := shiftedPolynomial a b n
  have hp : p≠0 := shiftedPolynomial_ne_zero ha hb n
  have ho : ∀ q : Polynomial ℝ,q.natDegree<p.natDegree →
      (∫ t in (0:ℝ)..1,weight a b t*(p.eval t*q.eval t))=0 := by
    intro q hq
    exact shiftedPolynomial_orthogonal_lower ha hb (by rwa [shiftedPolynomial_natDegree ha hb] at hq)
  obtain ⟨hcard,hinside⟩ := roots_of_orthogonality ha hb hp ho
  have hnodup : p.roots.Nodup := Multiset.nodup_iff_count_le_one.mpr (fun c => by
    rw [count_roots]
    exact simple_roots_of_orthogonality ha hb hp ho c)
  exact ⟨hcard.trans (shiftedPolynomial_natDegree ha hb n),hnodup,hinside,splits_iff_card_roots.mpr hcard⟩

end
end jacobi.Jacobi
