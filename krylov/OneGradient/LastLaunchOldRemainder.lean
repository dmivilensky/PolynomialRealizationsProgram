import krylov.Stability.C1VanishingProduct
import krylov.Stability.ContDiffSolve
import krylov.Correction.PairingOrders
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine incoming old-row quadratic remainder.
Use: compute the explicit incoming-gradient coefficient from the exact
actual model normal equation and observed conjugacy in either native basis.
Source: real first-order vanishing products, genuine replay-image order
and primitive-C1 coefficient freezing in actual operator increments.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Stability krylov.Correction
open scoped InnerProductSpace BigOperators
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] {p : ℕ}

/-- The exact actual last-launch normal equation and observed conjugacy
give the printed frozen old-direction drift coefficient with a genuine
quadratic remainder. Every increment remains its actual operator value.
Use: a common algebraic/calculus engine for the real S and D native
incoming-gradient calculations; D retains its actual quadratic image error.
Article: main_krylov, thm:local(a), original incoming old-row coefficient.
Proof: the model mismatch and actual correction weights both vanish at
the reference, so their true product is quadratic. Exact conjugacy leaves
only actual segment drift and replay error. Freeze the smooth old vector
and trial direction around that vanishing drift. The real incoming zero
allows its left old vector to be frozen as well; combine these actual errors. -/
theorem lastLaunch_old_row_remainder
    (s y : X → Fin p → E) (M : X → Matrix (Fin p) (Fin p) ℝ) (w : X → Fin p → ℝ)
    (G d : X → E) (tau : X → ℝ) (A : X → E →L[ℝ] E) (B : X → Fin p → E →L[ℝ] E)
    (hs : ∀ i,ContDiffAt ℝ 1 (fun z => s z i) 0)
    (hM : ∀ i j,ContDiffAt ℝ 1 (fun z => M z i j) 0)
    (hw : ∀ i,ContDiffAt ℝ 1 (fun z => w z i) 0)
    (hG : ContDiffAt ℝ 1 G 0) (hd : ContDiffAt ℝ 1 d 0) (htau : ContDiffAt ℝ 1 tau 0)
    (hA : ContDiffAt ℝ 1 A 0) (hB : ∀ i,ContDiffAt ℝ 1 (fun z => B z i) 0)
    (hzero : ∀ i,A 0=B 0 i) (hw0 : w 0=0) (hG0 : G 0=0)
    (hM0 : M 0=crossGram (s 0) (fun j => A 0 (s 0 j)))
    (hrow : ∀ᶠ z in 𝓝 (0 : X),coordinates (s z) (G z)=
      (crossGram (s z) (fun j => A z (s z j))-M z)*ᵥw z+tau z • coordinates (s z) (A z (d z)))
    (hconj : ∀ᶠ z in 𝓝 (0 : X),∀ i,inner ℝ (y z i) (d z)=0)
    (hsym : ∀ z i,(B z i).toLinearMap.IsSymmetric)
    (herror : ∀ i,(fun z => y z i-B z i (s z i)) =O[𝓝 0] (fun z => ‖z‖^2)) (i : Fin p) :
    (fun z => inner ℝ (s 0 i) (G z)-tau 0*inner ℝ (s 0 i) ((A z-B z i) (d 0)))
      =O[𝓝 0] (fun z => ‖z‖^2) := by
  let C := fun z (j : Fin p) => inner ℝ (s z i) (A z (s z j))-M z i j
  have hC (j : Fin p) : ContDiffAt ℝ 1 (fun z => C z j) 0 :=
    ((hs i).inner ℝ (hA.clm_apply (hs j))).sub (hM i j)
  have hC0 (j : Fin p) : C 0 j=0 := by simp only [C,hM0,crossGram,sub_self]
  have hprod (j : Fin p) : (fun z => C z j*w z j) =O[𝓝 0] (fun z => ‖z‖^2) := by
    have hc : (fun z => C z j) =O[𝓝 0] (fun z => ‖z‖) := by
      simpa only [hC0 j,sub_zero] using ((hC j).differentiableAt (by norm_num)).isBigO_sub.norm_right
    have hwj : (fun z => w z j) =O[𝓝 0] (fun z => ‖z‖) := by
      simpa only [hw0,Pi.zero_apply,sub_zero] using ((hw j).differentiableAt (by norm_num)).isBigO_sub.norm_right
    simpa only [← sq] using hc.mul hwj
  have hsum : (fun z => ∑ j : Fin p,C z j*w z j) =O[𝓝 0] (fun z => ‖z‖^2) := by
    exact (IsBigO.sum (fun j (_ : j∈(Finset.univ : Finset (Fin p))) => hprod j)).congr_left
      (fun z => by simp only [Finset.sum_apply])
  have hdb : d =O[𝓝 0] (fun _ => (1 : ℝ)) := hd.continuousAt.tendsto.isBigO_one ℝ
  have htb : tau =O[𝓝 0] (fun _ => (1 : ℝ)) := htau.continuousAt.tendsto.isBigO_one ℝ
  have herr : (fun z => tau z*inner ℝ (y z i-B z i (s z i)) (d z)) =O[𝓝 0] (fun z => ‖z‖^2) := by
    simpa only [one_mul,mul_one] using htb.mul (inner_order _ _ _ _ (herror i) hdb)
  let L := fun z => innerSL ℝ (s z i)
  let D := fun z => A z-B z i
  let v := fun z => tau z • d z
  have hL : ContDiffAt ℝ 1 L 0 := (innerSL ℝ).contDiff.contDiffAt.comp 0 (hs i)
  have hD : ContDiffAt ℝ 1 D 0 := hA.sub (hB i)
  have hv : ContDiffAt ℝ 1 v 0 := htau.smul hd
  have hD0 : D 0=0 := by dsimp only [D];rw [hzero i,sub_self]
  have hfreeze : (fun z => tau z*inner ℝ (s z i) ((A z-B z i) (d z))-
      tau 0*inner ℝ (s 0 i) ((A z-B z i) (d 0))) =O[𝓝 0] (fun z => ‖z‖^2) := by
    simpa only [L,D,v,innerSL_apply_apply,map_smul,real_inner_smul_right,smul_eq_mul] using
      c1_vanishing_middle_remainder L D v (hL.differentiableAt (by norm_num))
        (hD.differentiableAt (by norm_num)) (hv.differentiableAt (by norm_num)) hD0
  have hsDiff : (fun z => s z i-s 0 i) =O[𝓝 0] (fun z => ‖z‖) :=
    by simpa only [sub_zero] using ((hs i).differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hGbound : G =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [hG0,sub_zero] using (hG.differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hleft : (fun z => inner ℝ (s z i) (G z)-inner ℝ (s 0 i) (G z)) =O[𝓝 0] (fun z => ‖z‖^2) := by
    simpa only [inner_sub_left,← sq] using inner_order _ _ _ _ hsDiff hGbound
  apply (((hsum.add hfreeze).sub herr).sub hleft).congr' ?_ EventuallyEq.rfl
  filter_upwards [hrow,hconj] with z hz hc
  have hcoord := congrFun hz i
  change inner ℝ (s z i) (G z)=∑ j,C z j*w z j+tau z*inner ℝ (s z i) (A z (d z)) at hcoord
  have hcurv : inner ℝ (s z i) (A z (d z))=
      inner ℝ (s z i) ((A z-B z i) (d z))-inner ℝ (y z i-B z i (s z i)) (d z) := by
    have hb : inner ℝ (B z i (s z i)) (d z)=inner ℝ (s z i) (B z i (d z)) := hsym z i (s z i) (d z)
    rw [_root_.sub_apply,inner_sub_right,inner_sub_left,hc i,zero_sub,sub_neg_eq_add,hb]
    ring
  rw [hcurv] at hcoord
  nlinarith [hcoord]

end
end krylov.OneGradient
