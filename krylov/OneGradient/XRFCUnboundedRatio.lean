import krylov.OneGradient.ConcentratedComparison
import krylov.Reference.HeavyBallMatrix
set_option autoImplicit false
/-!
Article: main_krylov, prop:where, original unbounded actual XRFC/FC ratio.
Use: prove the initial launch term cannot be removed for any fixed number
of atoms >=2, even with uniform budgets and actual epsilon_j=1/2.
Source: actual concentrated full-atom physical gradients, true CG polynomial
energy bounds, genuine smooth half-CG policies and the existing positive
irreducible heavy-ball Jacobi realization in every finite dimension.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Envelope krylov.Realization
open scoped BigOperators
variable {n : ℕ}

/-- Even on a fixed actual positive matrix with distinct eigenvalues, the
original uniform-budget C_D/(epsBar*C_FC) is unbounded as the genuine initial
spectral weights concentrate, with actual smooth positive half-CG trials.
Use: the source counterexample remains in the original full-atom class and
uses a strictly positive real FC denominator.
Article: main_krylov, prop:where, necessity of the initial launch term.
Proof: choose the true maximal eigenmode, retain a small positive coefficient
on every other original mode, and use the proved actual FC bound n^2*s and
actual XRFC lower bound one half. The explicit parameter 1/(n^2*(M+1)) makes
the honest positive-denominator ratio exceed any supplied nonnegative M. -/
theorem xrfc_FC_ratio_unbounded_on_matrix
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hd : Function.Injective hb.1.eigenvalues) (hn : 2≤n) (M : ℝ) (hM : 0≤M) :
    ∃ g : EuclideanSpace ℝ (Fin n),referenceAtomCount base hb g=n ∧
      (∀ k<n,xrfcTrialError (halfCGTrial base g) base g k=1/2) ∧
      (∀ k<n,0<halfCGTrial base g (oneGradientRun (xrfcMethod fullMemory (halfCGTrial base g))
        (fun _ => cgOperator base) g k)) ∧
      (∀ k,ContDiff ℝ 2 (trialCoordinate (halfCGTrial base g) k)) ∧
      M<(∑ l∈Finset.range n,|xrfcTrialCoefficient (halfCGTrial base g) base g n l|)/
        ((1/2 : ℝ)*(∑ l∈Finset.range n,‖cgCanonicalError base g (l+1)‖)) := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨p,_,hmax'⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) hb.1.eigenvalues Finset.univ_nonempty
  have hmax (i : Fin n) : hb.1.eigenvalues i≤hb.1.eigenvalues p := hmax' i (Finset.mem_univ i)
  have hnreal : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hM1 : 0<M+1 := by linarith
  let s : ℝ := ((n : ℝ)^2*(M+1))⁻¹
  have hs : 0<s := inv_pos.mpr (mul_pos (sq_pos_of_pos hnreal) hM1)
  let g := concentratedGradient base hb p s
  have hcount : referenceAtomCount base hb g=n := concentrated_gradient_full_atoms base hb hd p s hs.ne'
  have hFC := concentrated_FC_constant_le base hb hd p hmax s hs (by omega)
  have hD := concentrated_XRFC_constant_ge base hb hd p hmax s hs (by omega)
  have hid : (n : ℝ)^2*s=(M+1)⁻¹ := by
    dsimp only [s]
    rw [_root_.mul_inv_rev]
    calc
      (n : ℝ)^2*((M+1)⁻¹*((n : ℝ)^2)⁻¹)=(M+1)⁻¹*((n : ℝ)^2*((n : ℝ)^2)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero 2 hnreal.ne'),mul_one]
  rw [hid] at hFC
  refine ⟨g,hcount,?_,?_,?_,?_⟩
  · intro k hk
    exact halfCGTrial_error base hb g k (by rw [hcount];exact hk)
  · intro k hk
    exact halfCGTrial_positive base hb g k (by rw [hcount];exact hk)
  · exact halfCGTrial_contDiff base g
  · have hden : 0<(1/2 : ℝ)*(∑ l∈Finset.range n,‖cgCanonicalError base g (l+1)‖) :=
      mul_pos (by norm_num) (full_FC_constant_pos base hb g hcount hn)
    apply (lt_div_iff₀ hden).mpr
    have hfrac : M/(M+1)<1 := (div_lt_one hM1).mpr (by linarith)
    have hsmall : M*((1/2 : ℝ)*(M+1)⁻¹)<1/2 := by
      have he : M*((1/2 : ℝ)*(M+1)⁻¹)=(1/2 : ℝ)*(M/(M+1)) := by rw [div_eq_mul_inv];ring
      rw [he]
      linarith
    have hprod := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFC (by norm_num : (0 : ℝ)≤1/2)) hM
    exact (hprod.trans_lt hsmall).trans_le hD

/-- For every fixed original atom count at least two, genuine full-atom
positive references and primitive smooth positive half-CG trials make the
actual original XRFC/FC sharp-constant ratio arbitrarily large.
Use: close the source's all-dimensions counterexample without a reference
existence or spectral-realization hypothesis.
Article: main_krylov, prop:where, unbounded ratio for every fixed n>=2.
Proof: the existing irreducible positive finite heavy-ball matrix supplies a
true n-atom first-site reference in every dimension. Its genuine full support
forces distinct eigenvalues. Apply the proved fixed-matrix concentration
family, preserving that original physical matrix and every real active atom. -/
theorem xrfc_FC_ratio_unbounded_every_dimension (n : ℕ) (hn : 2≤n) (M : ℝ) (hM : 0≤M) :
    ∃ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)),
      referenceAtomCount base hb g=n ∧
      (∀ k<n,xrfcTrialError (halfCGTrial base g) base g k=1/2) ∧
      (∀ k<n,0<halfCGTrial base g (oneGradientRun (xrfcMethod fullMemory (halfCGTrial base g))
        (fun _ => cgOperator base) g k)) ∧
      (∀ k,ContDiff ℝ 2 (trialCoordinate (halfCGTrial base g) k)) ∧
      M<(∑ l∈Finset.range n,|xrfcTrialCoefficient (halfCGTrial base g) base g n l|)/
        ((1/2 : ℝ)*(∑ l∈Finset.range n,‖cgCanonicalError base g (l+1)‖)) := by
  let base := heavyBallMatrix 1 (1/2) n
  have hb : base.PosDef := heavyBallMatrix_posDef 1 (1/2) (by norm_num) n
  let oldg : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (chebyshev1.JacobiData.site n 0)
  have hcount : referenceAtomCount base hb oldg=n := raw_referenceAtomCount base hb
    (heavyBallMatrix_tridiagonal 1 (1/2) n) (heavyBallMatrix_adjacent_neg 1 (1/2) (by norm_num) (by norm_num) n)
  have hd := (full_atoms_coordinates base hb oldg hcount).1
  obtain ⟨g,hg⟩ := xrfc_FC_ratio_unbounded_on_matrix base hb hd hn M hM
  exact ⟨base,hb,g,hg⟩

end
end krylov.OneGradient
