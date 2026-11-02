import krylov.Stability.CompactC1Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), genuine compact C-one moving-factor freezing.
Use: freeze real terminal paired steps and both outer factors of true fresh
defects with one quadratic bound on the original compact reference tube.
Source: proved genuine compact C-one field bounds, real Cauchy--Schwarz,
actual operator norms and exact bilinear difference identities.
-/

namespace krylov.Stability
noncomputable section
open Set
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- Freezing a true moving paired step against a true zero-reference terminal
gradient costs one common quadratic remainder under original C-one data.
Use: remove every actual moving-basis term in full-cycle reconstruction.
Article: main_krylov, apH:dcs2(b), compact terminal pairing freezing.
Proof: actual compact mean-value estimates make both the real step difference
and the real terminal gradient first order. Cauchy--Schwarz multiplies them. -/
theorem compact_terminal_pairing_freeze (s g : X → E) (K : Set X) (hK : IsCompact K)
    (hs : ∀ x∈K,ContDiffAt ℝ 1 s x) (hg : ∀ x∈K,ContDiffAt ℝ 1 g x)
    (hg0 : ∀ x∈K,g x=0) :
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ y : X,‖y-x‖≤delta →
      ‖inner ℝ (s y) (g y)-inner ℝ (s x) (g y)‖≤C*‖y-x‖^2 := by
  obtain ⟨ds,Ls,_,hds,hLs,_,_,hsbound⟩ := compact_c1_field_bounds s K hK hs
  obtain ⟨dg,Lg,_,hdg,hLg,_,_,hgbound⟩ := compact_c1_field_bounds g K hK hg
  refine ⟨min ds dg,Ls*Lg,lt_min hds hdg,mul_nonneg hLs hLg,?_⟩
  intro x hx y hy
  have hsd := (hsbound x hx y (hy.trans (min_le_left _ _))).1
  have hgd := (hgbound x hx y (hy.trans (min_le_right _ _))).1
  rw [hg0 x hx,sub_zero] at hgd
  rw [← inner_sub_left]
  calc
    _≤‖s y-s x‖*‖g y‖ := norm_inner_le_norm _ _
    _≤(Ls*‖y-x‖)*(Lg*‖y-x‖) := mul_le_mul hsd hgd (norm_nonneg _) (mul_nonneg hLs (norm_nonneg _))
    _=(Ls*Lg)*‖y-x‖^2 := by ring

/-- Both actual moving outer steps of a true fresh operator defect can be
frozen at their genuine reference values with one compact quadratic cost,
under C-one regularity alone.
Use: source fresh defects retain their actual operator difference while
all genuine moving-step effects become second order uniformly.
Article: main_krylov, apH:dcs2(b), compact true fresh outer-factor replacement.
Proof: the actual operator defect vanishes on the compact reference set and
therefore has a common linear bound. Split the exact bilinear difference into
one changed left factor and one changed right factor. Genuine compact step
increments and actual bounded reference/nearby vectors give the quadratic estimate. -/
theorem compact_fresh_pairing_freeze (u v : X → E) (T : X → E →L[ℝ] E)
    (K : Set X) (hK : IsCompact K)
    (hu : ∀ x∈K,ContDiffAt ℝ 1 u x) (hv : ∀ x∈K,ContDiffAt ℝ 1 v x)
    (hT : ∀ x∈K,ContDiffAt ℝ 1 T x) (hT0 : ∀ x∈K,T x=0) :
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ y : X,‖y-x‖≤delta →
      ‖inner ℝ (u y) (T y (v y))-inner ℝ (u x) (T y (v x))‖≤C*‖y-x‖^2 := by
  obtain ⟨du,Lu,Mu,hdu,hLu,hMu,huval,hubound⟩ := compact_c1_field_bounds u K hK hu
  obtain ⟨dv,Lv,Mv,hdv,hLv,hMv,_,hvbound⟩ := compact_c1_field_bounds v K hK hv
  obtain ⟨dt,Lt,_,hdt,hLt,_,_,hTbound⟩ := compact_c1_field_bounds T K hK hT
  refine ⟨min du (min dv dt),Lu*Lt*(Mv+Lv)+Mu*Lt*Lv,
    lt_min hdu (lt_min hdv hdt),by positivity,?_⟩
  intro x hx y hy
  have hud := (hubound x hx y (hy.trans (min_le_left _ _))).1
  have hvd := (hvbound x hx y (hy.trans ((min_le_right _ _).trans (min_le_left _ _)))).1
  have hvval := (hvbound x hx y (hy.trans ((min_le_right _ _).trans (min_le_left _ _)))).2
  have hTd := (hTbound x hx y (hy.trans ((min_le_right _ _).trans (min_le_right _ _)))).1
  rw [hT0 x hx,sub_zero] at hTd
  have hsplit : inner ℝ (u y) (T y (v y))-inner ℝ (u x) (T y (v x))=
      inner ℝ (u y-u x) (T y (v y))+inner ℝ (u x) (T y (v y-v x)) := by
    rw [inner_sub_left,map_sub,inner_sub_right]
    ring
  have hleft : ‖inner ℝ (u y-u x) (T y (v y))‖≤
      (Lu*‖y-x‖)*((Lt*‖y-x‖)*(Mv+Lv)) := by
    apply (norm_inner_le_norm _ _).trans
    apply mul_le_mul hud _ (norm_nonneg _) (mul_nonneg hLu (norm_nonneg _))
    exact ((T y).le_opNorm _).trans (mul_le_mul hTd hvval (norm_nonneg _) (mul_nonneg hLt (norm_nonneg _)))
  have hright : ‖inner ℝ (u x) (T y (v y-v x))‖≤
      Mu*((Lt*‖y-x‖)*(Lv*‖y-x‖)) := by
    apply (norm_inner_le_norm _ _).trans
    apply mul_le_mul (huval x hx) _ (norm_nonneg _) hMu
    exact ((T y).le_opNorm _).trans (mul_le_mul hTd hvd (norm_nonneg _) (mul_nonneg hLt (norm_nonneg _)))
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add hleft hright).trans_eq (by ring))

end
end krylov.Stability
