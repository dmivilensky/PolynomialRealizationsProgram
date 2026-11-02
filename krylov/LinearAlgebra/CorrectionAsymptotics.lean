import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Analysis.Normed.Operator.NormedSpace
import chebyshev1.Algebra.OrderedProduct

/-!
Article: main_krylov, apA:galerkin(a), first and repeated correction orders.
Use: derive perturbative orders from actual inverse-model correction operators;
all estimates use the spectral or Hilbert operator norm of the corresponding algebra.
Source: mathlib's proved Banach-algebra inverse expansion and the earlier article's
ordered product, with newest factors acting on the left.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Filter Asymptotics Topology
variable {α R : Type*} [NormedRing R] [HasSummableGeomSeries R] {f : Filter α}

/-- An actual inverse model near the identity differs from the identity by the same order.
Use: justify the inverse expansion before multiplying correction residuals.
Article: main_krylov, apA:galerkin(a), Ĵ⁻¹=I+O(ω).
Source: mathlib NormedRing.inverse_add_norm_diff_first_order.
Proof: the assumed model error tends to zero; compose the proved inverse expansion
with that actual error and then use its given order bound. -/
theorem inverse_near_identity_order (J : α → R) (s : α → ℝ)
    (hs : Tendsto s f (𝓝 0)) (hJ : (fun x => J x - 1) =O[f] s) :
    (fun x => Ring.inverse (J x) - 1) =O[f] s := by
  have ht := hJ.trans_tendsto hs
  have h := (NormedRing.inverse_add_norm_diff_first_order (1 : Rˣ)).comp_tendsto ht
  have he : ∀ x, (1 : R) + (J x - 1) = J x := fun x => by abel
  have hh : (fun x => Ring.inverse (J x) - 1) =O[f] (fun x => J x - 1) := by
    simpa only [Function.comp_def, Units.val_one, inv_one, he] using h.of_norm_right
  exact hh.trans hJ

/-- The true correction operator has its stated first-order leading term and quadratic error.
Use: the inverse model does not alter the first-order curvature mismatch.
Article: main_krylov, apA:galerkin(a), E Ĵ⁻¹=L+O(ω²).
Proof: split the difference into (E−L)Ĵ⁻¹+L(Ĵ⁻¹−I); the inverse is bounded
and its deviation has first order, so both products have quadratic order. -/
theorem correction_operator_order (J E L : α → R) (s : α → ℝ)
    (hs : Tendsto s f (𝓝 0)) (hJ : (fun x => J x - 1) =O[f] s)
    (hE : (fun x => E x - L x) =O[f] (fun x => s x ^ 2)) (hL : L =O[f] s) :
    (fun x => E x * Ring.inverse (J x) - L x) =O[f] (fun x => s x ^ 2) := by
  -- Continuity at the actual unit bounds the inverse before multiplying remainders.
  have hji := inverse_near_identity_order J s hs hJ
  have ht : Tendsto J f (𝓝 1) := by
    have h := (hJ.trans_tendsto hs).add_const (1 : R)
    simpa only [sub_add_cancel, zero_add] using h
  have hi : (fun x => Ring.inverse (J x)) =O[f] (fun _ => (1 : ℝ)) :=
    ((NormedRing.inverse_continuousAt (1 : Rˣ)).tendsto.comp ht).isBigO_one ℝ
  have ha : (fun x => (E x - L x) * Ring.inverse (J x)) =O[f] (fun x => s x ^ 2) := by
    simpa only [mul_one] using hE.mul hi
  have hb : (fun x => L x * (Ring.inverse (J x) - 1)) =O[f] (fun x => s x ^ 2) := by
    simpa only [← pow_two] using hL.mul hji
  have he : ∀ x, (E x - L x) * Ring.inverse (J x) + L x * (Ring.inverse (J x) - 1) =
      E x * Ring.inverse (J x) - L x := by intro x; noncomm_ring
  simpa only [he] using ha.add hb

section Action
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual operator actions multiply their scalar asymptotic orders.
Use: transfer canonical matrix/continuous-operator estimates to the true residual vectors.
Article: main_krylov, apA:galerkin(a), correction orders.
Proof: the operator-norm bound dominates every action by the product of its two norms. -/
theorem operator_action_order (T : α → V →L[ℝ] V) (v : α → V) (s t : α → ℝ)
    (hT : T =O[f] s) (hv : v =O[f] t) :
    (fun x => T x (v x)) =O[f] (fun x => s x * t x) := by
  have hb : (fun x => T x (v x)) =O[f] (fun x => ‖T x‖ * ‖v x‖) :=
    isBigO_of_le _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact (T x).le_opNorm (v x)
  exact hb.trans (hT.norm_left.mul hv.norm_left)

/-- One true correction raises the leading residual order by one and the remainder by two.
Use: applies to the actual canonical correction operator after correction_operator_order.
Article: main_krylov, apA:galerkin(a), ĝ₊=−Lr+O(ω^(p+2)).
Proof: expand the error as −(T−L)g−L(g−r); boundedness of the small scale
first puts g at order p, then both actual operator actions have order p+2. -/
theorem correction_vector_order (T L : α → V →L[ℝ] V) (g r : α → V) (s : α → ℝ)
    (p : ℕ) (hs : Tendsto s f (𝓝 0))
    (hT : (fun x => T x - L x) =O[f] (fun x => s x ^ 2)) (hL : L =O[f] s)
    (hg : (fun x => g x - r x) =O[f] (fun x => s x ^ (p + 1)))
    (hr : r =O[f] (fun x => s x ^ p)) :
    (fun x => -(T x (g x)) + L x (r x)) =O[f] (fun x => s x ^ (p + 2)) := by
  have hpow : (fun x => s x ^ (p + 1)) =O[f] (fun x => s x ^ p) := by
    simpa only [pow_succ, mul_one] using
      (isBigO_refl (fun x => s x ^ p) f).mul (hs.isBigO_one ℝ)
  have hgo : g =O[f] (fun x => s x ^ p) := by
    simpa only [sub_add_cancel] using (hg.trans hpow).add hr
  -- Keep the two sources of error separate until their powers have been matched.
  have ha := operator_action_order (fun x => T x - L x) g (fun x => s x ^ 2)
    (fun x => s x ^ p) hT hgo
  have hb := operator_action_order L (fun x => g x - r x) s
    (fun x => s x ^ (p + 1)) hL hg
  have ha' : (fun x => (T x - L x) (g x)) =O[f] (fun x => s x ^ (p + 2)) :=
    ha.congr_right fun x => by ring
  have hb' : (fun x => L x (g x - r x)) =O[f] (fun x => s x ^ (p + 2)) :=
    hb.congr_right fun x => by ring
  have he : ∀ x, -((T x - L x) (g x)) - L x (g x - r x) = -(T x (g x)) + L x (r x) := by
    intro x
    simp only [sub_apply, map_sub]
    abel
  simpa only [he] using ha'.neg_left.sub hb'

/-- The actual sequence of canonical corrected residuals for arbitrary varying models.
Use: every new operator acts on the residual left by the preceding correction.
Article: main_krylov, apA:galerkin(a), eq:correction-product. -/
def correctionRun (T : ℕ → α → V →L[ℝ] V) (g : α → V) : ℕ → α → V
  | 0 => g
  | k + 1 => fun x => -(T k x (correctionRun T g k x))

/-- Evaluating a correction run freezes only its external parameter, preserving every chronological factor.
Use: apply exact single-scenario algebra to a parametrized asymptotic product.
Article: main_krylov, thm:C2(b), evaluation of the actual finite product.
Proof: induction unfolds the same true correction recurrence on both sides. -/
theorem correctionRun_freeze (L : ℕ → α → V →L[ℝ] V) (r : α → V) (t : ℕ) (x : α) :
    correctionRun L r t x=correctionRun (fun j (_ : Unit) => L j x) (fun _ => r x) t () := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [correctionRun,ih]

/-- A fixed linear coordinate change intertwining every true factor intertwines their signed correction product.
Use: transfer native residual products into the genuine canonical metric without commuting factors.
Article: main_krylov, thm:C2(b), cancellation of intermediate model coordinates.
Proof: finite induction preserves the chronological order; linearity carries
the next residual sign and the assumed exact factor intertwining. -/
theorem correctionRun_map (L M : ℕ → α → V →L[ℝ] V) (r : α → V)
    (D : V →L[ℝ] V) (t : ℕ) (x : α)
    (hD : ∀ j<t, ∀ v, D (L j x v)=M j x (D v)) :
    D (correctionRun L r t x)=correctionRun M (fun z => D (r z)) t x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [correctionRun,map_neg,hD t (Nat.lt_succ_self t)]
    rw [ih (fun j hj => hD j (Nat.lt_succ_of_lt hj))]

/-- The leading correction recurrence is the signed ordered product with newest factor leftmost.
Use: matches the exact product order in the printed asymptotic expansion.
Article: main_krylov, apA:galerkin(a), (−1)^t L_t⋯L₁r.
Source: reuse chebyshev1.orderedProduct.
Proof: induction combines linearity of the next factor with the next scalar sign. -/
theorem correctionRun_orderedProduct (L : ℕ → α → V →L[ℝ] V) (r : α → V) (t : ℕ) (x : α) :
    correctionRun L r t x = ((-1 : ℝ) ^ t) •
      (chebyshev1.orderedProduct (fun k => L k x) t) (r x) := by
  induction t with
  | zero => simp [correctionRun]
  | succ t ih =>
    change -(L t x (correctionRun L r t x)) = _
    rw [ih, map_smul, chebyshev1.orderedProduct_succ]
    simp only [mul_apply_eq_comp, pow_succ, mul_neg_one, neg_smul]

/-- Products of t first-order correction factors have the exact residual order p+t.
Use: supply the leading-order premise for the next correction without an assumed expansion.
Article: main_krylov, apA:galerkin(a), finite correction product order.
Proof: induct on the actual correction recurrence, multiplying its two scalar orders. -/
theorem correctionRun_order (L : ℕ → α → V →L[ℝ] V) (r : α → V) (s : α → ℝ)
    (p t : ℕ) (hL : ∀ k < t, L k =O[f] s) (hr : r =O[f] (fun x => s x ^ p)) :
    correctionRun L r t =O[f] (fun x => s x ^ (p + t)) := by
  -- Each newest factor is applied on the left to the actual previous residual.
  induction t with
  | zero => simpa only [correctionRun, Nat.add_zero] using hr
  | succ t ih =>
    have hprev := ih (fun k hk => hL k (Nat.lt_succ_of_lt hk))
    have h := (operator_action_order (L t) (correctionRun L r t) s
      (fun x => s x ^ (p + t)) (hL t (Nat.lt_succ_self t)) hprev).neg_left
    exact h.congr_right fun x => by simp only [pow_succ', Nat.add_succ]

/-- Every fixed finite number of actual corrections has the printed leading product
and a remainder one order smaller than that product acting on r.
Use: closes the repeated-correction asymptotic claim for arbitrary varying correction operators.
Article: main_krylov, apA:galerkin(a), eq:correction-product.
Proof: finite induction applies the proved one-correction error theorem to the
actual residual and the recursively constructed leading product. -/
theorem repeated_correction_order (T L : ℕ → α → V →L[ℝ] V) (g r : α → V)
    (s : α → ℝ) (p t : ℕ) (hs : Tendsto s f (𝓝 0))
    (hT : ∀ k < t, (fun x => T k x - L k x) =O[f] (fun x => s x ^ 2))
    (hL : ∀ k < t, L k =O[f] s)
    (hg : (fun x => g x - r x) =O[f] (fun x => s x ^ (p + 1)))
    (hr : r =O[f] (fun x => s x ^ p)) :
    (fun x => correctionRun T g t x - correctionRun L r t x) =O[f]
      (fun x => s x ^ (p + t + 1)) := by
  -- The induction hypothesis measures the true trajectory against its explicit leading product.
  induction t with
  | zero => simpa only [correctionRun, Nat.add_zero] using hg
  | succ t ih =>
    have ht := ih (fun k hk => hT k (Nat.lt_succ_of_lt hk))
      (fun k hk => hL k (Nat.lt_succ_of_lt hk))
    have hl := correctionRun_order L r s p t (fun k hk => hL k (Nat.lt_succ_of_lt hk)) hr
    have h := correction_vector_order (T t) (L t) (correctionRun T g t) (correctionRun L r t)
      s (p + t) hs (hT t (Nat.lt_succ_self t)) (hL t (Nat.lt_succ_self t)) ht hl
    simpa only [correctionRun, sub_neg_eq_add, Nat.add_assoc] using h

end Action

end
end krylov.LinearAlgebra
