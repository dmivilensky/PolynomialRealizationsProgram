import krylov.Reference.ConcentratedCG
import krylov.OneGradient.HalfCGTrial
set_option autoImplicit false
/-!
Article: main_krylov, prop:where, actual separated FC and XRFC constants.
Use: estimate both original sharp coefficients on a genuine full-atom
physical reference family with actual smooth half-CG trial policies.
Source: actual CG polynomial minimum, original Pythagorean first energy,
real measured half-error amplitudes and the true finite source constants.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Envelope krylov.Variation
open scoped BigOperators
variable {n : ℕ}

/-- The actual original uniform-budget FC sharp coefficient tends to zero
in the genuine full-atom concentrated reference family.
Use: quantify the numerator/denominator separation in the source counterexample.
Article: main_krylov, prop:where.
Proof: every true positive-horizon CG energy has the same genuine linear
competitor bound. Its square root is at most n*s; summing the n original
nonnegative error-profile terms gives the stated physical coefficient bound. -/
theorem concentrated_FC_constant_le
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hd : Function.Injective hb.1.eigenvalues) (p : Fin n)
    (hmax : ∀ i,hb.1.eigenvalues i≤hb.1.eigenvalues p) (s : ℝ) (hs : 0<s) (hn : 1≤n) :
    (∑ l∈Finset.range n,‖cgCanonicalError base (concentratedGradient base hb p s) (l+1)‖)≤(n : ℝ)^2*s := by
  have hsub : ((n-1 : ℕ) : ℝ)≤n := by exact_mod_cast Nat.sub_le n 1
  have hnreal : (1 : ℝ)≤n := by exact_mod_cast hn
  have hfactor : ((n-1 : ℕ) : ℝ)≤(n : ℝ)^2 := by nlinarith
  have hterm (l : ℕ) (hl : l<n) :
      ‖cgCanonicalError base (concentratedGradient base hb p s) (l+1)‖≤(n : ℝ)*s := by
    have h := concentrated_cg_error base hb hd p hmax s hs.ne' (l+1) (by omega) (by omega)
    have hsquare := h.trans (mul_le_mul_of_nonneg_right hfactor (sq_nonneg s))
    rw [← mul_pow] at hsquare
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg n) hs.le)).mp hsquare
  have hsum := Finset.sum_le_sum (fun l hl => hterm l (Finset.mem_range.mp hl))
  calc
    _ ≤ ∑ _l∈Finset.range n,(n : ℝ)*s := hsum
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,pow_two,mul_assoc]

/-- The true direction-basis XRFC uniform-budget sharp constant stays at
least one half on the same original full-atom concentrated physical family.
Use: every measured trial error is one half while the actual launch remains large.
Article: main_krylov, prop:where.
Proof: the actual first amplitude is one half of the true first square-root
CG energy, which is at least one. Every other actual absolute amplitude is
nonnegative, so its first genuine term bounds the original finite sharp sum below. -/
theorem concentrated_XRFC_constant_ge
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hd : Function.Injective hb.1.eigenvalues) (p : Fin n)
    (hmax : ∀ i,hb.1.eigenvalues i≤hb.1.eigenvalues p) (s : ℝ) (hs : 0<s) (hn : 1≤n) :
    (1 : ℝ)/2≤∑ l∈Finset.range n,|xrfcTrialCoefficient
      (halfCGTrial base (concentratedGradient base hb p s)) base (concentratedGradient base hb p s) n l| := by
  have hcount := concentrated_gradient_full_atoms base hb hd p s hs.ne'
  have hfirst := concentrated_first_energy base hb hd p hmax s hs.ne' hn
  have hzero : 0<n := by omega
  have hamp := halfCGTrial_amplitude base hb (concentratedGradient base hb p s) n (by rw [hcount]) 0 hzero
  have hone : (1 : ℝ)/2≤|xrfcTrialCoefficient
      (halfCGTrial base (concentratedGradient base hb p s)) base (concentratedGradient base hb p s) n 0| := by
    rw [hamp]
    linarith
  exact hone.trans (Finset.single_le_sum
    (f := fun l : ℕ => |xrfcTrialCoefficient (halfCGTrial base (concentratedGradient base hb p s))
      base (concentratedGradient base hb p s) n l|)
    (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hzero))

/-- The actual FC comparison denominator is strictly positive for every true
full-atom reference with at least two atoms.
Use: the unbounded-ratio statement uses an honest real quotient rather than
relying on a totalized division by a zero FC constant.
Article: main_krylov, prop:where.
Proof: actual full activity makes the first post-search error nonzero; its
positive norm is one real term of the original nonnegative FC profile sum. -/
theorem full_FC_constant_pos
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n) (hn : 2≤n) :
    0<∑ l∈Finset.range n,‖cgCanonicalError base g (l+1)‖ := by
  have htail := remainingTail_ne_zero base hb g 0 (by rw [hc];omega)
  change -cgCanonicalError base g 1≠0 at htail
  have he : cgCanonicalError base g 1≠0 := neg_ne_zero.mp htail
  have hpos := norm_pos_iff.mpr he
  exact hpos.trans_le (Finset.single_le_sum (f := fun l : ℕ => ‖cgCanonicalError base g (l+1)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega : 0<n)))

end
end krylov.OneGradient
