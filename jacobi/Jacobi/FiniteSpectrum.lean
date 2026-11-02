import jacobi.Jacobi.Nodes
import jacobi.Jacobi.ZeroTransfer

/-!
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
The actual ordered Jacobi roots define exactly the source's squared
spectral zeros and scaled resolvent values. Positivity, ordering and
complete agreement with the genuine scaled hypergeometric zero set
are proved before taking any spectral limit.
Source: the proved full Jacobi zero theorem and the literal edge scaling.
Use: the canonical finite zero sequence whose fixed-index limit is the actual Bessel sigma sequence.
-/
namespace jacobi.Jacobi
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

/-- The actual finite squared-edge spectral zeros in increasing order.
Use: the canonical finite zero sequence whose fixed-index limit is the actual Bessel sigma sequence.
Article: jacobi, Lemma 1.3.
-/
def finiteSigma (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (i : Fin n) : ℝ :=
  4*(n:ℝ)^2*shiftedRoots a b ha hb n i

/-- The actual scaled finite Jacobi resolvent eigenvalues in decreasing order.
Use: finite first and second spectral traces and the source L1 spectral limit.
Article: jacobi, Lemma 1.3.
-/
def finiteLambda (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (i : Fin n) : ℝ :=
  2/finiteSigma a b ha hb n i

/-- Every finite squared spectral zero is positive, and the finite list strictly increases.
Use: all genuine finite spectral reciprocals are well-defined and canonically ordered.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: the actual shifted roots are positive and strictly increase; multiplication by the positive scale preserves their order. -/
theorem finiteSigma_properties {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn : 0<n) :
    (∀ i:Fin n,0<finiteSigma a b ha hb n i) ∧ StrictMono (finiteSigma a b ha hb n) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hscale : 0<4*(n:ℝ)^2 := by positivity
  exact ⟨fun i => mul_pos hscale (shiftedRoots_properties ha hb i).2.1,
    fun i j hij => mul_lt_mul_of_pos_left ((shiftedRoots a b ha hb n).strictMono hij) hscale⟩

/-- The actual finite squared spectral zero has exactly the source's node formula.
Use: transfers the special-function zero limit to resolvents in every existing finite polynomial fibre.
Article: jacobi, Lemma 1.3.
Proof: substitute the literal affine Jacobi node and collect the positive scaling factors. -/
theorem finiteSigma_node {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (i : Fin n) :
    finiteSigma a b ha hb n i=2*(n:ℝ)^2*(1-(nodes a b ha hb n).value i) := by
  dsimp [finiteSigma,nodes]
  ring

/-- Every actual finite spectral reciprocal is precisely the source's scaled resolvent value.
Use: the finite spectral sequences and the earlier finite-fibre matrix spectra agree with their original definitions.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: replace the squared spectral zero by its exact node formula and cancel the constant factor two. -/
theorem finiteLambda_node {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (i : Fin n) :
    finiteLambda a b ha hb n i=1/((n:ℝ)^2*(1-(nodes a b ha hb n).value i)) := by
  rw [finiteLambda,finiteSigma_node ha hb i,mul_assoc,div_mul_eq_div_div]
  norm_num

/-- The actual real scaled Jacobi function is exactly the shifted polynomial in its spectral coordinate.
Use: the complete finite root enumeration applies directly to the same functions in the proved Mehler--Heine theorem.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: the proved affine evaluation identity and elementary rational scaling identify the two actual finite functions. -/
theorem scaledReal_eq_shifted (a b x : ℝ) (n : ℕ) :
    scaledReal a b n x=(shiftedPolynomial a b n).eval (x/(4*(n:ℝ)^2)) := by
  rw [shiftedPolynomial_eval]
  unfold scaledReal
  congr 1
  ring

/-- The genuine scaled Jacobi function vanishes exactly at the actual canonical finite squared spectral zeros.
Use: identifies every locally transferred Bessel zero with an original finite Jacobi spectral index.
Article: jacobi, Lemma 1.3.
Proof: the real scaled function is the shifted polynomial at z/(4*n^2).
Use the proved complete root enumeration and cancel only the nonzero
degree scale. Reality identifies these real zeros with the original complex function. -/
theorem finiteSigma_zero_iff {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn : 0<n) (x : ℝ) :
    normalized (a:ℂ) (b:ℂ) n (1-(x:ℂ)/(2*(n:ℂ)^2))=0 ↔
      ∃ i:Fin n,finiteSigma a b ha hb n i=x := by
  -- Every zero and every enumeration term comes from the same actual finite polynomial.
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have he : 1-(x:ℂ)/(2*(n:ℂ)^2)=((1-x/(2*(n:ℝ)^2):ℝ):ℂ) := by push_cast; rfl
  rw [he,← realNormalized_zero_iff]
  change scaledReal a b n x=0 ↔ _
  rw [scaledReal_eq_shifted,shiftedRoots_exhaustive ha hb n]
  apply exists_congr
  intro i
  unfold finiteSigma
  rw [eq_div_iff (show 4*(n:ℝ)^2≠0 by positivity),mul_comm (shiftedRoots a b ha hb n i)]

end
end jacobi.Jacobi
