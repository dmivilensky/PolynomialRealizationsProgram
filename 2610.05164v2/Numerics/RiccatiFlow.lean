import «2610.05164v2».Numerics.RiccatiBounds
import «2610.05164v2».Numerics.Quadrature
import Mathlib.Analysis.ODE.ExistUnique

/-!
Article: 2610.05164v2, Lemma 21.
Scalar one-sided stability for validated Riccati integration.
Use: `«2610.05164v2».Numerics.riccati_stability` feeds
`«2610.05164v2».Numerics.riccati_taylor_propagation` (riccati taylor propagation).
Proof chain: `«2610.05164v2».Numerics.riccati_taylor_propagation` — 2610.05164v2, Lemma 21;
Validated signed-slope flow: existence, uniqueness and Taylor propagation.
Source: Teschl, Ordinary Differential Equations and Dynamical Systems — scalar Gronwall comparison.
The needed form is proved here.
-/
namespace «2610.05164v2».Numerics
noncomputable section
open Set Real MeasureTheory intervalIntegral
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
The stated quantitative bound `|e t|≤|e a| *exp (L*(t-a))`.

Use: `«2610.05164v2».Numerics.riccati_stability` uses this bound to establish the stated
quantitative bound `|y t-z t|≤r*exp (L*(t-a))`.

Article: 2610.05164v2, Lemma 21 via `«2610.05164v2».Numerics.riccati_unique`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — scalar Gronwall
comparison.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem signed_linear_stability {e q : ℝ → ℝ} {a b L : ℝ}
    (he : ContinuousOn e (Icc a b))
    (hd : ∀ t∈Ioo a b, HasDerivAt e (q t*e t) t)
    (hq : ∀ t∈Ioo a b, q t≤L) {t : ℝ} (ht : t∈Icc a b) :
    |e t|≤|e a| *exp (L*(t-a)) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  let w := fun t => e t^2*exp (-2*L*(t-a))
  -- Establish continuity hw before using the function at limits or in calculus arguments.
  have hw : ContinuousOn w (Icc a b) := by
    apply he.pow 2 |>.mul
    fun_prop
  have hwd : ∀ x∈Ioo a b, HasDerivAt w
      (2*(q x-L)*e x^2*exp (-2*L*(x-a))) x := by
    intro x hx
    convert ((hd x hx).pow 2).mul
      ((((hasDerivAt_id x).sub_const a).const_mul (-2*L)).exp) using 1
    · rfl
    · simp only [Pi.pow_apply,id_eq]
      ring
  have hm : AntitoneOn w (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hw
    · intro x hx
      rw [interior_Icc] at hx
      exact (hwd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hwd x hx).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith [hq x hx]) (sq_nonneg _)) (exp_pos _).le
  have hh := hm ⟨le_rfl,ht.1.trans ht.2⟩ ht ht.1
  have hex : exp (-2*L*(t-a))*exp (2*L*(t-a))=1 := by
    rw [← exp_add]
    convert exp_zero using 2; ring
  have hs : e t^2≤(|e a| *exp (L*(t-a)))^2 := by
    have hh' := mul_le_mul_of_nonneg_right hh (exp_pos (2*L*(t-a))).le
    dsimp [w] at hh'
    simp only [sub_self,mul_zero,exp_zero,mul_one] at hh'
    have hex2 : exp (2*L*(t-a))=exp (L*(t-a))^2 := by
      rw [← exp_nat_mul]
      congr 1
      ring
    calc
      e t^2=e t^2*(exp (-2*L*(t-a))*exp (2*L*(t-a))) := by rw [hex,mul_one]
      _≤e a^2*exp (2*L*(t-a)) := by simpa only [mul_assoc] using hh'
      _=(|e a| *exp (L*(t-a)))^2 := by rw [hex2,mul_pow,sq_abs]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (abs_nonneg _) (exp_pos _).le)).mp
    (by simpa only [sq_abs] using hs)

/--
The stated quantitative bound `|y t-z t|≤r*exp (L*(t-a))`.

Use: `«2610.05164v2».Numerics.riccati_taylor_propagation` uses this bound to establish the
stated quantitative bound `|y (a+v)-∑ j∈Finset.range (N+1),normalizedWithin z (Icc a (a+h)) j
a*v^j| ≤R*v^(N+1)+r*exp (L*v)`.

Article: 2610.05164v2, Lemma 21 via `«2610.05164v2».Numerics.riccati_taylor_propagation`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — scalar Gronwall
comparison.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.signed_linear_stability` with the
arguments shown in the proof.
-/
theorem riccati_stability {C A B y z : ℝ → ℝ} {a b l u L r : ℝ}
    (hy : ContinuousOn y (Icc a b)) (hz : ContinuousOn z (Icc a b))
    (hdy : ∀ t∈Ioo a b,HasDerivAt y (C t+A t*y t+B t*y t^2) t)
    (hdz : ∀ t∈Ioo a b,HasDerivAt z (C t+A t*z t+B t*z t^2) t)
    (hyY : ∀ t∈Icc a b,y t∈Icc l u) (hzY : ∀ t∈Icc a b,z t∈Icc l u)
    (hL : ∀ t∈Ioo a b,∀ v∈Icc l u,A t+2*B t*v≤L)
    (hr : |y a-z a|≤r) {t : ℝ} (ht : t∈Icc a b) :
    |y t-z t|≤r*exp (L*(t-a)) := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.signed_linear_stability` with the
  -- arguments shown in the proof.
  have he := signed_linear_stability (e := fun t => y t-z t)
    (q := fun t => A t+B t*(y t+z t)) (hy.sub hz)
    (fun t ht => by convert (hdy t ht).sub (hdz t ht) using 1; ring)
    (fun t ht => by
      have hyy := hyY t ⟨ht.1.le,ht.2.le⟩
      have hzz := hzY t ⟨ht.1.le,ht.2.le⟩
      have hm : (y t+z t)/2∈Icc l u := ⟨by linarith [hyy.1,hzz.1],by linarith [hyy.2,hzz.2]⟩
      convert hL t ht _ hm using 1; ring) ht
  exact he.trans (mul_le_mul_of_nonneg_right hr (exp_pos _).le)

end
end «2610.05164v2».Numerics
