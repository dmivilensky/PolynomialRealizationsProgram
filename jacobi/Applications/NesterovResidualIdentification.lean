import jacobi.Applications.NesterovIdentification
import jacobi.Applications.BlockTerminal
import jacobi.Applications.NesterovFull

/-!
Article: jacobi, Proposition A.1.
The actual general-momentum realization has literally the same residual
polynomial as the previously analysed source Gegenbauer factorization.
Thus its true original iterates inherit the full complex hard-edge limit
and the complete genuinely numbered small-zero geometry.
Use: Article checks the source proposition for the original recurrence.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial Real Set Filter chebyshev1
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- On the original spectral half-line the actual Nesterov transfer equals the literal source Gegenbauer residual for every original positive iteration count and admissible momentum parameter.
Use: nesterov_original_residual obtains equality of the two actual polynomials, then transfers the complete complex hard-edge theorem to the original iteration.
Article: jacobi, Proposition A.1.
Proof: substitute the genuine nonnegative square root in the independently proved actual error formula. The true normalized symmetric Jacobi polynomial is the genuine Gegenbauer quotient, and its integer square-root power equals the printed real-power prefactor. No spectral endpoint is cancelled. -/
theorem nesterov_original_eval {b:ℝ} (hb:-1<b) {k:ℕ} (hk:0<k) {l:ℝ} (hl:l≤1) :
    ((nesterovMethod b).residualPolynomial k).eval l=(nesterovAt b k).eval l := by
  -- Both source objects are identified through the actual original error recurrence, with all original normalizations retained.
  have hs:sqrt (1-l)^2=1-l:=sq_sqrt (by linarith)
  have he:=nesterovError_square hb (sqrt (1-l)) (k-1)
  rw [hs,sub_sub_cancel,show k-1+1=k by omega,show k-1+2=k+1 by omega] at he
  have hg:= jacobi.Jacobi.symmetricUnit_gegenbauer (a:=b/2) (by linarith) (k-1) (sqrt (1-l))
  rw [show b/2+1/2=(b+1)/2 by ring] at hg
  have hp:=nesterovAt_sqrt_formula hb hk hl
  have hpow:(1-l)^(((k+1:ℕ):ℝ)/2)=sqrt (1-l)^(k+1):=by
    simpa only [Real.rpow_natCast] using Real.rpow_div_two_eq_sqrt (x:=1-l) ((k+1:ℕ):ℝ) (by linarith)
  rw [hpow,← hg,← Complex.ofReal_mul] at hp
  have haeval:(aeval (l:ℂ) (nesterovAt b k))=(((nesterovAt b k).eval l:ℝ):ℂ):=
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A:=ℂ) l _
  rw [haeval] at hp
  have hr:=congrArg Complex.re hp
  simp only [Complex.ofReal_re] at hr
  rw [Realization.residualPolynomial_eval,nesterov_transfer,he]
  exact hr.symm

/-- Every genuine positive-count original Nesterov realization has exactly the actual source Gegenbauer residual polynomial for every b>-1.
Use: the complete complex hard-edge theorem and the true exhaustive small-zero description apply directly to the actual original recurrence.
Article: jacobi, Proposition A.1.
Proof: both original polynomials agree at every lambda<=1, an infinite set, by the actual recurrence identification. Polynomial identity therefore extends the same equality to every real and complex evaluation. -/
theorem nesterov_original_residual {b:ℝ} (hb:-1<b) {k:ℕ} (hk:0<k) :
    (nesterovMethod b).residualPolynomial k=nesterovAt b k := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Iic_infinite (1:ℝ)).mono
  intro l hl
  exact nesterov_original_eval hb hk hl

/-- The genuine original Nesterov recurrence has the full printed entire Bessel hard-edge limit uniformly on every compact complex set.
Use: Article checks the hard-edge claim for the actual original realization, with the recurrence-to-residual identification fully proved.
Article: jacobi, Proposition A.1.
Proof: at every positive original iteration count the actual realization polynomial is exactly the same source polynomial whose complete uniform hard-edge limit is already proved. The single unused zero count has no effect on convergence. -/
theorem nesterov_original_hard_edge_uniform {b:ℝ} (hb:-1<b) {K:Set ℂ} (hK:IsCompact K) :
    TendstoUniformlyOn (fun k:ℕ=>fun z:ℂ=>aeval (z^2/(k:ℂ)^2)
      ((nesterovMethod b).residualPolynomial k))
      (fun z=> jacobi.Bessel.normalized ((b/2:ℝ):ℂ) (z^2)) atTop K := by
  apply (nesterov_all_hard_edge_uniform hb hK).congr
  filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk z _
  rw [nesterov_original_residual hb hk]

/-- The original recurrence's complete interior zero list is precisely the genuine increasing Jacobi list used in the proved Bessel zero limit.
Use: together with nesterov_all_small_zero_limit, this supplies exactly the source proposition's original numbered small-zero assertion.
Article: jacobi, Proposition A.1.
Proof: substitute the actual proved original residual-polynomial equality into the already proved exhaustive factorized-polynomial zero description. -/
theorem nesterov_original_small_zero_iff {b:ℝ} (hb:-1<b) {k:ℕ} (hk:0<k) {x:ℝ}
    (hx:x∈Ioo (0:ℝ) 1) :
    ((nesterovMethod b).residualPolynomial k).eval x=0 ↔
      ∃ i:Fin ((k-1)/2),nesterovSmallZeros b hb ((k-1)%2) ((k-1)/2) i=x := by
  rw [nesterov_original_residual hb hk]
  exact nesterovAt_small_zero_iff hb k hx

/-- Every actual interior zero of the genuine original Nesterov realization is simple for every original admissible momentum parameter.
Use: Article combines the exhaustive original zero ordering with its already proved Bessel limit, preserving the source's genuine simple-zero geometry.
Article: jacobi, Proposition A.1.
Proof: literal equality of the actual original residual polynomials transfers root multiplicity to the genuine Jacobi-factor polynomial, whose interior roots are already proved simple. -/
theorem nesterov_original_small_zero_simple {b:ℝ} (hb:-1<b) {k:ℕ} (hk:0<k) {x:ℝ}
    (hx:x∈Ioo (0:ℝ) 1) (hz:((nesterovMethod b).residualPolynomial k).eval x=0) :
    ((nesterovMethod b).residualPolynomial k).rootMultiplicity x=1 := by
  rw [nesterov_original_residual hb hk] at hz ⊢
  exact nesterov_small_zero_simple hb ((k-1)%2) ((k-1)/2) hx hz

/-- The actual fixed-matrix operator transfer of the original Nesterov realization is evaluation of precisely the same genuine source Gegenbauer residual.
Use: Article checks that the original recurrence-to-polynomial bridge concerns the actual transfer on every original finite-dimensional physical space.
Article: jacobi, Proposition A.1.
Proof: reuse the first article's exact generic operator-polynomial semantics and substitute the independently proved literal original residual identity. -/
theorem nesterov_original_operator {b:ℝ} (hb:-1<b) {k:ℕ} (hk:0<k)
    {d:Type*} [Fintype d] [DecidableEq d] (H:Matrix d d ℝ) :
    (nesterovMethod b).operatorTransfer k (fun _=>H)=aeval H (nesterovAt b k) := by
  rw [Realization.operatorTransfer_eq_aeval,nesterov_original_residual hb hk]

end
end jacobi.Applications
