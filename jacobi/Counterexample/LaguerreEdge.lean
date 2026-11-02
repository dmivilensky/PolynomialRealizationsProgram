import jacobi.Counterexample.LaguerrePolynomial
import jacobi.Laguerre.SpectralLimit
import jacobi.GelfandLevitan.HalfSineCase

/-!
Article: jacobi, Proposition 6.1.
The actual source nodes are 1-y_(n,k)/H_n, and the zero-padded scaled
resolvents are exactly H_n/n times the original Laguerre reciprocal
spectrum. Their actual total mass and ordered-coordinate limits give
the printed l1 limit 2/(theta*pi^2*k^2), including the entire tail.
Use: laguerreEdge is the literal scaled resolvent spectrum of the original polynomial p_n^L.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix Polynomial Set Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The source's original finite Laguerre nodes in descending order.
Use: laguerreEdge is the literal scaled resolvent spectrum of the original polynomial p_n^L.
Article: jacobi, Proposition 6.1.
-/
def laguerreNode (theta:ℝ) (n:ℕ) (i:Fin n) : ℝ :=
  1- jacobi.Laguerre.roots (1/2) (by norm_num) n i/laguerreScale theta n

/-- Every actual source Laguerre node is a genuine root of the literal printed counterexample polynomial.
Use: laguerreEdge is the true original polynomial's resolvent sequence rather than an independently specified approximation.
Article: jacobi, Proposition 6.1.
Proof: the nonzero original H_n cancels in H_n*(1-zeta). The
actual classical Laguerre factor vanishes at its proved original root. -/
theorem laguerreNode_is_root {theta:ℝ} (ht:0 < theta) (n:ℕ) (i:Fin n) :
    (laguerrePolynomial theta n).eval (laguerreNode theta n i)=0 := by
  -- The root equation uses the exact source polynomial and its original classical normalization.
  have hH:laguerreScale theta n≠0:=(laguerreScale_pos ht n).ne'
  have harg:laguerreScale theta n*(1-laguerreNode theta n i)=
      jacobi.Laguerre.roots (1/2) (by norm_num) n i := by
    unfold laguerreNode
    field_simp
    ring
  simp only [laguerrePolynomial,eval_mul,eval_C,eval_comp,eval_sub,eval_one,eval_X,harg,
    jacobi.Laguerre.classical,jacobi.Laguerre.roots_is_zero (by norm_num : (-1:ℝ)<1/2),mul_zero]

/-- The original Laguerre source nodes are strictly descending.
Use: laguerreNode_exhaustive retains the article's genuine finite ordering in the complete scaled spectrum.
Article: jacobi, Proposition 6.1.
Proof: the actual Laguerre roots strictly increase and division by the positive original H_n preserves their strict order. -/
theorem laguerreNode_strictAnti {theta:ℝ} (ht:0 < theta) (n:ℕ) : StrictAnti (laguerreNode theta n) := by
  intro i j hij
  have hh:=div_lt_div_of_pos_right
    ((jacobi.Laguerre.roots (1/2) (by norm_num) n).strictMono hij) (laguerreScale_pos ht n)
  exact sub_lt_sub_left hh 1

/-- The original Laguerre source polynomial vanishes exactly at the complete canonically ordered source node list.
Use: the printed full edge-spectrum limit concerns every original root of p_n^L and has no omitted finite modes.
Article: jacobi, Proposition 6.1.
Proof: its actual nonzero factorial and scale factor reduce vanishing
to the original normalized Laguerre polynomial at H_n*(1-x). The proved
complete root enumeration and this invertible affine change give the exact index. -/
theorem laguerreNode_exhaustive {theta:ℝ} (ht:0 < theta) (n:ℕ) (x:ℝ) :
    (laguerrePolynomial theta n).eval x=0 ↔ ∃i:Fin n,laguerreNode theta n i=x := by
  -- Both directions preserve the complete original finite polynomial, not only its limiting zeros.
  have hH:laguerreScale theta n≠0:=(laguerreScale_pos ht n).ne'
  have hF:(n.factorial:ℝ)≠0:=by exact_mod_cast Nat.factorial_ne_zero n
  have hD:(ascPochhammer ℝ n).eval ((1/2:ℝ)+1)≠0:=
    (jacobi.Laguerre.denominator_pos (by norm_num : (-1:ℝ)<1/2) n).ne'
  simp only [laguerrePolynomial,eval_mul,eval_C,eval_comp,eval_sub,eval_one,eval_X,
    jacobi.Laguerre.classical,mul_eq_zero,div_ne_zero hF (pow_ne_zero n hH),
    div_ne_zero hD hF,false_or]
  rw [jacobi.Laguerre.roots_zero_iff (by norm_num : (-1:ℝ)<1/2)]
  apply exists_congr
  intro i
  unfold laguerreNode
  constructor <;> intro hi <;> field_simp [hH] at hi ⊢ <;> linarith

/-- The source's actual zero-padded scaled Laguerre resolvent spectrum.
Use: laguerreEdge_l1_limit proves the full infinite-tail conclusion in the original printed normalization.
Article: jacobi, Proposition 6.1.
-/
def laguerreEdge (theta:ℝ) (n k:ℕ) : ℝ :=
  if hk:k < n then 1/((n:ℝ)^2*(1-laguerreNode theta n ⟨k,hk⟩)) else 0

/-- The original Laguerre scaled resolvent is exactly H_n/n times its true reciprocal-root spectrum.
Use: laguerreEdge_l1_limit transfers both the actual coordinate limits and exact full spectral mass from the proved Laguerre matrix theory.
Article: jacobi, Proposition 6.1.
Proof: on every genuine finite node substitute zeta=1-y/H and
cancel only the actual positive H_n, dimension and original Laguerre
root. Both sides have the same genuine zero padding. -/
theorem laguerreEdge_eq {theta:ℝ} (ht:0 < theta) {n:ℕ} (hn:0 < n) (k:ℕ) :
    laguerreEdge theta n k=(laguerreScale theta n/(n:ℝ))*
      jacobi.Laguerre.scaledInverse (1/2) (by norm_num) n k := by
  -- This identity retains the original dimension-squared resolvent normalization.
  unfold laguerreEdge jacobi.Laguerre.scaledInverse
  by_cases hk:k < n
  · rw [dite_eq_left hk,dite_eq_left hk,laguerreNode]
    have hH:laguerreScale theta n≠0:=(laguerreScale_pos ht n).ne'
    have hN:(n:ℝ)≠0:=Nat.cast_ne_zero.mpr hn.ne'
    have hy: jacobi.Laguerre.roots (1/2) (by norm_num) n ⟨k,hk⟩≠0:=
      (jacobi.Laguerre.roots_pos (by norm_num) _).ne'
    rw [show 1-(1- jacobi.Laguerre.roots (1/2) (by norm_num) n ⟨k,hk⟩/laguerreScale theta n)=
      jacobi.Laguerre.roots (1/2) (by norm_num) n ⟨k,hk⟩/laguerreScale theta n by ring]
    field_simp [hH,hN,hy]
  · simp only [hk,dite_false,mul_zero]

/-- The entire original Laguerre source resolvent spectrum converges in l1 to theta^(-1) times the true U edge spectrum.
Use: laguerreEdge_l1_printed states the same full result with the explicit source values 2/(theta*pi^2*k^2).
Article: jacobi, Proposition 6.1.
Proof: the original finite spectra are positive and summable. Their
coordinates converge by the actual Laguerre zero limit and H_n/n
limit. Their complete total masses converge by the exact inverse-root
sum. The existing discrete Scheffe theorem controls the whole infinite tail. -/
theorem laguerreEdge_l1_limit {theta:ℝ} (ht:0 < theta) :
    Tendsto (fun n:ℕ=>∑'k,|laguerreEdge theta (n+1) k-
      (1/theta)* jacobi.Bessel.edgeValue (1/2) (by norm_num) k|) atTop (𝓝 0) := by
  -- Every condition is proved for the actual source nodes; no finite-spectrum tail bound is assumed.
  let ha:(-1:ℝ)<1/2:=by norm_num
  have hs:∀n,Summable (laguerreEdge theta (n+1)) := by
    intro n
    have he:laguerreEdge theta (n+1)=fun k=>
        (laguerreScale theta (n+1)/((n+1:ℕ):ℝ))* jacobi.Laguerre.scaledInverse (1/2) ha (n+1) k :=
      funext (laguerreEdge_eq ht (Nat.succ_pos n))
    rw [he]
    exact (jacobi.Laguerre.scaledInverse_summable ha (n+1)).mul_left _
  have hpos:∀n k,0≤laguerreEdge theta (n+1) k := by
    intro n k
    rw [laguerreEdge_eq ht (Nat.succ_pos n)]
    exact mul_nonneg (div_nonneg (laguerreScale_pos ht _).le (Nat.cast_nonneg _))
      (jacobi.Laguerre.scaledInverse_nonneg ha _ _)
  have hp (k:ℕ) : Tendsto (fun n:ℕ=>laguerreEdge theta (n+1) k) atTop
      (𝓝 ((1/theta)* jacobi.Bessel.edgeValue (1/2) ha k)) := by
    have h:=(laguerre_scale_limit ht).mul
      ((jacobi.Laguerre.scaledInverse_limit ha k).comp (tendsto_add_atTop_nat 1))
    have hv:(1/(2*theta))*(2* jacobi.Bessel.edgeValue (1/2) ha k)=
        (1/theta)* jacobi.Bessel.edgeValue (1/2) ha k:=by field_simp
    rw [hv] at h
    apply (tendsto_congr ?_).mpr h
    intro n
    simpa only [Nat.cast_succ,Function.comp_def] using laguerreEdge_eq ht (Nat.succ_pos n) k
  apply jacobi.Jacobi.nonnegative_scheffe hs
    ((jacobi.Bessel.edgeValue_summable ha).mul_left (1/theta)) hpos
    (fun k=>mul_nonneg (by positivity) ((jacobi.Bessel.edgeValue_properties ha).1 k).le) hp
  have he (n:ℕ) : (∑'k,laguerreEdge theta (n+1) k)=
      (laguerreScale theta (n+1)/((n:ℝ)+1))*(2/3) := by
    simp_rw [laguerreEdge_eq ht (Nat.succ_pos n)]
    rw [tsum_mul_left,jacobi.Laguerre.scaledInverse_mass ha (Nat.succ_pos n)]
    norm_num
  simp_rw [he]
  rw [tsum_mul_left,jacobi.Bessel.first_rayleigh_sum ha]
  have h:=(laguerre_scale_limit ht).mul_const (2/3:ℝ)
  have hv:(1/theta)*(1/(2*((1/2:ℝ)+1)))=(1/(2*theta))*(2/3) := by norm_num; field_simp
  rw [hv]
  exact h

/-- The full original Laguerre scaled resolvent spectrum has the printed l1 limit, including every padded mode and its infinite tail.
Use: this is the Laguerre edge-spectrum assertion paired with laguerre_polynomial_minimum_limit in Proposition 6.1.
Article: jacobi, Proposition 6.1.
Proof: substitute the proved actual U spectrum sigma_k=pi^2*k^2
in the genuine full l1 limit; elementary field algebra gives exactly
the original printed spectral normalization. -/
theorem laguerreEdge_l1_printed {theta:ℝ} (ht:0 < theta) :
    Tendsto (fun n:ℕ=>∑'k,|laguerreEdge theta (n+1) k-
      2/(theta*Real.pi^2*(k+1:ℝ)^2)|) atTop (𝓝 0) := by
  have he (k:ℕ) : (1/theta)* jacobi.Bessel.edgeValue (1/2) (by norm_num) k=
      2/(theta*Real.pi^2*(k+1:ℝ)^2) := by
    rw [jacobi.Bessel.edgeValue,jacobi.GelfandLevitan.half_sine_spectrum]
    field_simp
  simpa only [he] using laguerreEdge_l1_limit ht

end
end jacobi.Counterexample
