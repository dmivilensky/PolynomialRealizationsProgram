import polyak.Numerics.Parametric.FiniteFamily
import polyak.Numerics.Parametric.CorrelatedEndpoint

/-!
Article: Appendix B, gluing a checked ordered continuation chain.
Use: nonadjacent slabs are disjoint. At each shared endpoint a checked Newton
image transfers the left root into the right box, where uniqueness identifies it.
-/
noncomputable section
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

structure ChainFamily {n k : ℕ} (F : Fin n → Expr) (cfg : DyadicConfig)
    (slabs : Fin (k+1) → Slab n) : Prop where
  checked : ∀ i,checkCorrelated F (slabs i).domain (slabs i).certificate cfg=true
  seam : ∀ i : Fin k,(slabs i.castSucc).domain.hi=(slabs i.succ).domain.lo
  gap : ∀ i j,i.val+1<j.val →
    (slabs i).domain.hi<(slabs j).domain.lo
  linked : ∀ i : Fin k,checkCorrelatedEndpoint F
    (slabs i.castSucc).certificate (slabs i.succ).certificate
    (slabs i.castSucc).domain.hi cfg=true

namespace ChainFamily
variable {n k : ℕ} {F : Fin n → Expr} {cfg : DyadicConfig}
  {slabs : Fin (k+1) → Slab n} (chain : ChainFamily F cfg slabs)
include chain

theorem adjacent_equal (i : Fin k) {s : ℝ}
    (hl : s∈(slabs i.castSucc).domain) (hr : s∈(slabs i.succ).domain)
    {x y : Fin n → ℝ}
    (hx : FinBoxMem x (coordinateBox (slabs i.castSucc).certificate.center
      (slabs i.castSucc).certificate.radius)) (hFx : system F s x=0)
    (hy : FinBoxMem y (coordinateBox (slabs i.succ).certificate.center
      (slabs i.succ).certificate.radius)) (hFy : system F s y=0) : x=y := by
  have he : s=((slabs i.castSucc).domain.hi : ℝ) := by
    have hh : ((slabs i.castSucc).domain.hi : ℝ)=
        ((slabs i.succ).domain.lo : ℝ) := by rw [chain.seam i]
    have hl' := hl.2
    have hr' := hr.1
    linarith
  have hx' := checkCorrelatedEndpoint_sound F (slabs i.castSucc).certificate
    (slabs i.succ).certificate (slabs i.castSucc).domain.hi cfg (chain.linked i) hx
      (by rwa [← he])
  exact (checkCorrelated_sound F (slabs i.succ).domain (slabs i.succ).certificate cfg
    (chain.checked i.succ) s hr).unique ⟨hx',hFx⟩ ⟨hy,hFy⟩

theorem forward_equal {i j : Fin (k+1)} (hij : i.val<j.val) {s : ℝ}
    (hi : s∈(slabs i).domain) (hj : s∈(slabs j).domain)
    {x y : Fin n → ℝ}
    (hx : FinBoxMem x (coordinateBox (slabs i).certificate.center (slabs i).certificate.radius))
    (hFx : system F s x=0)
    (hy : FinBoxMem y (coordinateBox (slabs j).certificate.center (slabs j).certificate.radius))
    (hFy : system F s y=0) : x=y := by
  have hnext : j.val=i.val+1 := by
    by_contra he
    have hgap : i.val+1<j.val := by omega
    have hg : ((slabs i).domain.hi : ℝ)<((slabs j).domain.lo : ℝ) :=
      by exact_mod_cast chain.gap i j hgap
    have hl' := hi.2
    have hr' := hj.1
    linarith
  let a : Fin k := ⟨i.val,by omega⟩
  have hai : a.castSucc=i := Fin.ext rfl
  have haj : a.succ=j := Fin.ext (by simpa only [Fin.val_succ] using hnext.symm)
  exact chain.adjacent_equal a (by simpa only [hai] using hi)
    (by simpa only [haj] using hj) (by simpa only [hai] using hx) hFx
    (by simpa only [haj] using hy) hFy

theorem compatibleFamily : CompatibleFamily F cfg slabs where
  checked := chain.checked
  compatible := by
    intro i j s hi hj x y hx hFx hy hFy
    rcases lt_trichotomy i.val j.val with hij|hij|hij
    · exact chain.forward_equal hij hi hj hx hFx hy hFy
    · have he : i=j := Fin.ext hij
      subst j
      exact (checkCorrelated_sound F (slabs i).domain (slabs i).certificate cfg
        (chain.checked i) s hi).unique ⟨hx,hFx⟩ ⟨hy,hFy⟩
    · exact (chain.forward_equal hij hj hi hy hFy hx hFx).symm

end ChainFamily
end polyak.Numerics.Parametric
