import chebyshev1.Perturbations.PointwiseTaylor
import chebyshev1.Perturbations.ThirdDerivative

/-! The entire initial vector, rather than a fixed ray, tends to zero in the
second variation of the actual nonlinear recurrence. -/
namespace chebyshev1
noncomputable section
open Filter Set Asymptotics
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

namespace Perturbations
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem bilinear_littleO_left (B : E →L[ℝ] E →L[ℝ] F) {f g : E → E}
    (hf : f =o[𝓝 0] (fun x => x)) (hg : g =O[𝓝 0] (fun x => x)) :
    (fun x => B (f x) (g x)) =o[𝓝 0] (fun x : E => ‖x‖^2) := by
  simpa only [pow_two] using B.isBoundedBilinearMap.isBigO_comp.trans_isLittleO
    (hf.norm_norm.mul_isBigO hg.norm_norm)

theorem bilinear_littleO_right (B : E →L[ℝ] E →L[ℝ] F) {f g : E → E}
    (hf : f =O[𝓝 0] (fun x => x)) (hg : g =o[𝓝 0] (fun x => x)) :
    (fun x => B (f x) (g x)) =o[𝓝 0] (fun x : E => ‖x‖^2) :=
  bilinear_littleO_left B.flip hg hf

end Perturbations

namespace TwoTerm
variable {d : Type*} [Fintype d] [DecidableEq d]

def quadraticErrorCLM (S : TwoTerm) (H : Matrix d d ℝ) (n : ℕ) :
    (d → ℝ) →L[ℝ] (d → ℝ) :=
  (((S.realization.operatorTransfer n (fun _ => H)).mulVecLin)).toContinuousLinearMap

theorem quadraticErrorCLM_apply (S : TwoTerm) (H : Matrix d d ℝ) (n : ℕ) (v : d → ℝ) :
    S.quadraticErrorCLM H n v = S.quadraticError H v n :=
  (S.quadraticError_eq_transfer H v n).symm

theorem nonlinearError_hasFDerivAt (S : TwoTerm) (g : (d → ℝ) → d → ℝ)
    (hg : DifferentiableAt ℝ g 0) (hg0 : g 0 = 0) (n : ℕ) :
    HasFDerivAt (fun v => S.nonlinearError g v n)
      (S.quadraticErrorCLM (gradientLinearization g) n) 0 := by
  have hz (s : ℕ) : S.nonlinearError g 0 s = 0 := S.nonlinearError_zero g hg0 s
  induction n using Nat.twoStepInduction with
  | zero =>
    have hlin : S.quadraticErrorCLM (gradientLinearization g) 0 =
        ContinuousLinearMap.id ℝ (d → ℝ) := by
      ext v i
      rw [quadraticErrorCLM_apply]
      rfl
    rw [hlin]
    exact hasFDerivAt_id _
  | one =>
    have hh := (hasFDerivAt_id (0 : d → ℝ)).sub (hg.hasFDerivAt.const_smul (S.gamma 0))
    have hlin : S.quadraticErrorCLM (gradientLinearization g) 1 =
        ContinuousLinearMap.id ℝ (d → ℝ)-S.gamma 0 • fderiv ℝ g 0 := by
      ext v i
      simp [quadraticErrorCLM_apply, quadraticError, gradientLinearization_mulVec]
    rw [hlin]
    convert hh using 1
    funext v
    rfl
  | more n ih0 ih1 =>
    have hgr : HasFDerivAt g (fderiv ℝ g 0) (S.nonlinearError g 0 (n+1)) := by
      rw [hz]
      exact hg.hasFDerivAt
    have hc := hgr.comp (0 : d → ℝ) ih1
    have hh := ((ih1.const_smul (S.a (n+1))).add (ih0.const_smul (S.b (n+1)))).sub
      (hc.const_smul (S.gamma (n+1)))
    have hlin : S.quadraticErrorCLM (gradientLinearization g) (n+2) =
        S.a (n+1) • S.quadraticErrorCLM (gradientLinearization g) (n+1) +
        S.b (n+1) • S.quadraticErrorCLM (gradientLinearization g) n-
        S.gamma (n+1) • (fderiv ℝ g 0).comp (S.quadraticErrorCLM (gradientLinearization g) (n+1)) := by
      ext v i
      simp [quadraticErrorCLM_apply, quadraticError, gradientLinearization_mulVec]
    rw [hlin]
    convert hh using 1
    funext v
    rfl

/-- Full-vector Peano expansion under pointwise second differentiability of the
gradient, with the actual derivative tensor and actual nonlinear execution. -/
theorem nonlinearError_vector_second_order (S : TwoTerm) (g : (d → ℝ) → d → ℝ)
    (hg : ∀ᶠ x in 𝓝 (0 : d → ℝ), DifferentiableAt ℝ g x)
    (h2 : DifferentiableAt ℝ (fderiv ℝ g) 0) (hg0 : g 0 = 0) (N : ℕ) :
    (fun v => S.nonlinearError g v N-
      (S.quadraticError (gradientLinearization g) v N+S.quadraticCorrection g v N))
      =o[𝓝 0] (fun v : d → ℝ => ‖v‖^2) := by
  let H := gradientLinearization g
  let e := fun s v => S.nonlinearError g v s
  let a := fun s v => S.quadraticError H v s
  let B := fderiv ℝ (fderiv ℝ g) 0
  let R := fun s v => (g (e s v)-H.mulVec (e s v))-(1/2:ℝ) • B (a s v) (a s v)
  let L := fun s => -(S.gamma s) • (S.forcingTail H N s).toContinuousLinearMap
  have hgAt : DifferentiableAt ℝ g 0 := hg.self_of_nhds
  have hder (s : ℕ) := S.nonlinearError_hasFDerivAt g hgAt hg0 s
  have he0 (s : ℕ) : e s 0 = 0 := S.nonlinearError_zero g hg0 s
  have heO (s : ℕ) : e s =O[𝓝 0] (fun v => v) := by
    simpa only [S.nonlinearError_zero g hg0 s, sub_zero] using (hder s).isBigO_sub
  have haO (s : ℕ) : a s =O[𝓝 0] (fun v => v) := by
    have hh := (S.quadraticErrorCLM H s).isBigO_id (𝓝 0)
    change (fun v => S.quadraticErrorCLM H s v) =O[𝓝 0] (fun v => v) at hh
    simpa only [quadraticErrorCLM_apply] using hh
  have hea (s : ℕ) : (fun v => e s v-a s v) =o[𝓝 0] (fun v => v) := by
    simpa only [S.nonlinearError_zero g hg0 s, sub_zero, quadraticErrorCLM_apply] using (hder s).isLittleO
  have hR (s : ℕ) : R s =o[𝓝 0] (fun v : d → ℝ => ‖v‖^2) := by
    have hcomp := (Perturbations.pointwise_second_order_taylor g hg h2).comp_tendsto
      (show Tendsto (e s) (𝓝 0) (𝓝 0) by
        simpa only [S.nonlinearError_zero g hg0 s] using (hder s).continuousAt.tendsto)
    have ht := hcomp.trans_isBigO ((heO s).norm_norm.pow 2)
    have hleft := Perturbations.bilinear_littleO_left B (hea s) (heO s)
    have hright := Perturbations.bilinear_littleO_right B (haO s) (hea s)
    have hd := (hleft.add hright).const_smul_left (1/2:ℝ)
    convert ht.add hd using 1
    funext v
    simp only [Function.comp_def, R, H, B, gradientLinearization_mulVec, hg0, sub_zero,
      map_sub, sub_apply, Pi.smul_apply, smul_add, smul_sub]
    module
  have hL (s : ℕ) : (fun v => L s (R s v)) =o[𝓝 0] (fun v : d → ℝ => ‖v‖^2) :=
    ((L s).isBigO_comp _ (𝓝 0)).trans_isLittleO (hR s)
  have hsum := IsLittleO.sum (s := Finset.range N) (fun s _ => hL s)
  have hforcing (v : d → ℝ) : (∑ s ∈ Finset.range N, L s (g (e s v)-H.mulVec (e s v))) =
      ∑ s ∈ Finset.range N, S.forcingTail H N s (-(S.gamma s • (g (e s v)-H.mulVec (e s v)))) := by
    apply Finset.sum_congr rfl
    intro s _
    simp only [L, smul_apply, LinearMap.coe_toContinuousLinearMap', map_neg, map_smul, neg_smul]
  have hcorrection (v : d → ℝ) : (∑ s ∈ Finset.range N, L s ((1/2:ℝ) • B (a s v) (a s v))) =
      S.quadraticCorrection g v N := rfl
  convert hsum using 1
  funext v
  simp only [Finset.sum_apply, R, map_sub, Finset.sum_sub_distrib]
  have hforcing' := hforcing v
  simp only [map_sub, Finset.sum_sub_distrib] at hforcing'
  rw [hforcing', hcorrection, S.nonlinearError_eq_quadratic_add_forcing g H v N]
  change _ = (∑ s ∈ Finset.range N, S.forcingTail H N s
    (-(S.gamma s • (g (e s v)-H.mulVec (e s v)))))-S.quadraticCorrection g v N
  abel

end TwoTerm
end
end chebyshev1
