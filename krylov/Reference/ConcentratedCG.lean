import krylov.Reference.SpectralConcentration
set_option autoImplicit false
/-!
Article: main_krylov, prop:where, actual concentrated CG tail estimates.
Use: derive the small FC error profile and nonvanishing first trial energy
for the genuine full-atom physical concentration family.
Source: original canonical polynomial Parseval, a normalized degree-one
competitor at the maximal true eigenvalue and the actual CG energy minimum.
-/

namespace krylov.Reference
noncomputable section
open Matrix Polynomial krylov.Secant
open scoped BigOperators InnerProductSpace
variable {n : ℕ}

/-- The genuine maximal-atom degree-one competitor removes the unit mode
and leaves at most n-minus-one squared small coefficients.
Use: estimate actual CG outputs on original full-atom physical references.
Article: main_krylov, prop:where.
Proof: actual spectral coordinates are one on the chosen maximal eigenmode
and s elsewhere. The normalized polynomial vanishes at that eigenvalue and
has absolute value at most one on the entire true positive spectrum. Real
Parseval and the exact remaining-mode count give the original tail bound. -/
theorem concentrated_linear_competitor
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (p : Fin n)
    (hmax : ∀ i,hb.1.eigenvalues i≤hb.1.eigenvalues p) (s : ℝ) :
    ‖canonicalPolynomial base (concentratedGradient base hb p s)
      (1-C (hb.1.eigenvalues p)⁻¹*X)‖^2≤(n-1 : ℕ)*s^2 := by
  let q : ℝ[X] := 1-C (hb.1.eigenvalues p)⁻¹*X
  have hval (i : Fin n) : q.eval (hb.1.eigenvalues i)=1-hb.1.eigenvalues i/hb.1.eigenvalues p := by
    simp only [q,eval_sub,eval_one,eval_mul,eval_C,eval_X,div_eq_mul_inv,mul_comm]
  have hq0 : q.eval (hb.1.eigenvalues p)=0 := by rw [hval,div_self (hb.eigenvalues_pos p).ne',sub_self]
  have hq (i : Fin n) : (q.eval (hb.1.eigenvalues i))^2≤1 := by
    have hpos : 0≤hb.1.eigenvalues i/hb.1.eigenvalues p := div_nonneg (hb.eigenvalues_pos i).le (hb.eigenvalues_pos p).le
    have hle : hb.1.eigenvalues i/hb.1.eigenvalues p≤1 := (div_le_one (hb.eigenvalues_pos p)).mpr (hmax i)
    have habs : |q.eval (hb.1.eigenvalues i)|≤1 := by rw [hval,abs_le];constructor <;> linarith
    simpa only [sq_abs,one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr habs
  have hcoord := (concentrated_gradient_coordinates base hb p s).2
  have hterm (i : Fin n) : (inner ℝ (hb.1.eigenvectorBasis i)
      (cgCanonicalError base (concentratedGradient base hb p s) 0))^2*
      (q.eval (hb.1.eigenvalues i))^2≤ if i=p then 0 else s^2 := by
    rw [hcoord i]
    split_ifs with he
    · subst i
      simp only [hq0,zero_pow (by decide : 2≠0),mul_zero,le_refl]
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left (hq i) (sq_nonneg s)
  have hsum : (∑ i : Fin n,if i=p then (0 : ℝ) else s^2)=(n-1 : ℕ)*s^2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ p)]
    simp only [ite_true,add_zero]
    calc
      _ = ∑ _i∈Finset.univ.erase p,s^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ite_eq_right (Finset.mem_erase.mp hi).1]
      _ = _ := by simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [canonicalPolynomial_parseval base hb]
  exact (Finset.sum_le_sum (fun i _ => hterm i)).trans_eq hsum

/-- Every noninitial actual CG error of the original full-atom concentration
family is bounded by the same genuine small spectral tail.
Use: bound the whole original FC sharp error-profile coefficient uniformly in time.
Article: main_krylov, prop:where.
Proof: every positive horizon admits the same normalized linear polynomial;
the actual full atom count supplies the genuine CG minimum domain, so the
proved physical competitor bound applies to every real computed CG iterate. -/
theorem concentrated_cg_error
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hd : Function.Injective hb.1.eigenvalues) (p : Fin n)
    (hmax : ∀ i,hb.1.eigenvalues i≤hb.1.eigenvalues p) (s : ℝ) (hs : s≠0)
    (k : ℕ) (hk : 1≤k) (hkn : k≤n) :
    ‖cgCanonicalError base (concentratedGradient base hb p s) k‖^2≤(n-1 : ℕ)*s^2 := by
  let q : ℝ[X] := 1-C (hb.1.eigenvalues p)⁻¹*X
  have hcount := concentrated_gradient_full_atoms base hb hd p s hs
  have hdeg : q.natDegree≤k := by
    apply (natDegree_sub_le _ _).trans
    exact max_le (by simp)
      ((natDegree_C_mul_le _ X).trans (by simpa using hk))
  have hzero : q.eval 0=1 := by simp only [q,eval_sub,eval_one,eval_mul,eval_C,eval_X,mul_zero,sub_zero]
  have h := cg_energy_minimum base hb (concentratedGradient base hb p s) (by rw [hcount];exact hkn) hdeg hzero
  exact h.trans (concentrated_linear_competitor base hb p hmax s)

/-- The genuine first CG energy in the concentrated full-atom family stays
at least one while every later error tends to zero.
Use: the initial XRFC launch term cannot be bounded by the original FC tail sum.
Article: main_krylov, prop:where.
Proof: subtract the proved small first post-search energy from the exact
original initial energy in the genuine CG energy-drop identity, then take
nonnegative square roots. -/
theorem concentrated_first_energy
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hd : Function.Injective hb.1.eigenvalues) (p : Fin n)
    (hmax : ∀ i,hb.1.eigenvalues i≤hb.1.eigenvalues p) (s : ℝ) (hs : s≠0) (hn : 1≤n) :
    1≤Real.sqrt (cgEnergy base (concentratedGradient base hb p s) 0) := by
  have htail := concentrated_cg_error base hb hd p hmax s hs 1 le_rfl hn
  have hdrop := cgEnergy_drop base hb (concentratedGradient base hb p s) 0
  rw [concentrated_initial_energy] at hdrop
  have henergy : 1≤cgEnergy base (concentratedGradient base hb p s) 0 := by nlinarith
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt henergy

end
end krylov.Reference
