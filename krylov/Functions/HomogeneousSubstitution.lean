import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, genuine general
homogeneous-response substitution.
Use: propagate actual first jets through a genuine continuous d-linear
response, retaining an explicit uniform polynomial error bound for every
degree, including degree zero. No asymptotic response is postulated here.
Source: mathlib's exact multilinear finite telescoping estimate and scalar
homogeneity, both applied to the actual response map.
-/

namespace krylov.Functions
noncomputable section
open scoped BigOperators
variable {d : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The genuine diagonal homogeneous polynomial of a real continuous
d-linear response. Article: main_krylov, lem:cycle-transfer. -/
def homogeneousResponse (P : ContinuousMultilinearMap ℝ (fun _ : Fin d => V) W) (v : V) : W :=
  P (fun _ => v)

/-- A true d-linear diagonal response has exactly degree d under real scaling.
Article: main_krylov, lem:cycle-transfer. -/
theorem homogeneousResponse_smul
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin d => V) W) (c : ℝ) (v : V) :
    homogeneousResponse P (c • v)=c^d • homogeneousResponse P v := by
  simpa only [homogeneousResponse,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    P.map_smul_univ (fun _ : Fin d => c) (fun _ => v)

/-- The genuine degree-d diagonal response obeys its standard explicit
bounded-ball telescoping estimate, with all degree-zero cases included.
Article: main_krylov, lem:cycle-transfer. -/
theorem homogeneousResponse_sub_le
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin d => V) W) (x y : V) :
    ‖homogeneousResponse P x-homogeneousResponse P y‖ ≤
      ‖P‖*d*(max ‖x‖ ‖y‖)^(d-1)*‖x-y‖ := by
  cases d with
  | zero =>
    have heq : (fun _ : Fin 0 => x)=(fun _ => y) := by ext i; exact Fin.elim0 i
    simp only [homogeneousResponse,heq,sub_self,norm_zero,Nat.cast_zero,mul_zero,zero_mul,le_refl]
  | succ d =>
    have hb := P.norm_image_sub_le (fun _ : Fin (d+1) => x) (fun _ => y)
    have hfun : (fun _ : Fin (d+1) => x)-(fun _ => y)=(fun _ => x-y) := rfl
    simpa only [homogeneousResponse,Fintype.card_fin,hfun,pi_norm_const] using hb

/-- True source first-jet bounds give the explicit degree-d response error
at the original, unnormalized scale. Article: main_krylov, lem:cycle-transfer.
The factor epsilon^d is proved from actual multilinearity, rather than
assumed in a leading-response field. -/
theorem homogeneousResponse_jet_bound
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin d => V) W)
    (x v : V) (ε B τ : ℝ) (hε : 0<ε) (hB : 0≤B)
    (hx : ‖x‖≤B*ε) (hv : ‖v‖≤B) (hjet : ‖x-ε • v‖≤τ*ε) :
    ‖homogeneousResponse P x-ε^d • homogeneousResponse P v‖ ≤
      (‖P‖*d*B^(d-1)*τ)*ε^d := by
  cases d with
  | zero =>
    have heq : (fun _ : Fin 0 => x)=(fun _ => v) := by ext i; exact Fin.elim0 i
    simp only [homogeneousResponse,heq,pow_zero,one_smul,sub_self,norm_zero,
      Nat.cast_zero,mul_zero,zero_mul,le_refl]
  | succ d =>
    have hτ : 0≤τ := by nlinarith only [hjet,norm_nonneg (x-ε • v),hε]
    have hsv : ‖ε • v‖≤B*ε := by
      rw [norm_smul,Real.norm_of_nonneg hε.le]
      nlinarith only [mul_le_mul_of_nonneg_left hv hε.le]
    rw [← homogeneousResponse_smul]
    have hb := homogeneousResponse_sub_le P x (ε • v)
    calc
      _ ≤ ‖P‖*((d+1 : ℕ) : ℝ)*(B*ε)^d*(τ*ε) := by
        simp only [Nat.add_sub_cancel] at hb
        exact hb.trans (by gcongr; exact max_le hx hsv)
      _ = _ := by rw [mul_pow,pow_succ]; push_cast; ring

end
end krylov.Functions
