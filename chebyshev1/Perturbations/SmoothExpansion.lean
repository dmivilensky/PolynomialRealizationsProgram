import chebyshev1.Perturbations.Duhamel
import chebyshev1.Perturbations.Radial
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Operator.Asymptotics
import Mathlib.Analysis.Calculus.Gradient.Basic
import chebyshev1.Nonlinear.LipschitzHessian

/-! The second variation of the actual nonlinear run, derived from local smoothness. -/
namespace chebyshev1
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set Asymptotics
open scoped Topology BigOperators

namespace Perturbations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The local second Taylor expansion uses the actual first and second derivatives. -/
theorem second_order_taylor (f : ℝ → E) (hf : ContDiffAt ℝ 2 f 0) :
    (fun r => f r - (f 0 + r • deriv f 0 + r ^ 2 • ((1 / 2 : ℝ) • deriv (deriv f) 0)))
      =o[𝓝 0] (fun r : ℝ => r ^ 2) := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn le_rfl (by norm_num)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hU
  let s : Set ℝ := Metric.ball 0 ε
  have hs0 : (0 : ℝ) ∈ s := by simpa [s] using hε
  have hsU : s ⊆ U := hsub
  have hsnhds : s ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hε
  have hunique : UniqueDiffOn ℝ s := (Metric.isOpen_ball : IsOpen s).uniqueDiffOn
  have h1 : iteratedDerivWithin 1 f s 0 = deriv f 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hunique (hf.of_le (by norm_num)) hs0]
    simp [iteratedDeriv_eq_iterate]
  have h2 : iteratedDerivWithin 2 f s 0 = deriv (deriv f) 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hunique hf hs0]
    simp [iteratedDeriv_eq_iterate, Function.iterate_succ_apply]
  have hp (r : ℝ) : taylorWithinEval f 2 s 0 r =
      f 0 + r • deriv f 0 + r ^ 2 • ((1 / 2 : ℝ) • deriv (deriv f) 0) := by
    rw [taylorWithinEval_succ f 1 s 0 r, taylorWithinEval_succ f 0 s 0 r]
    simp [h1, h2, smul_smul, mul_comm]
    norm_num
  have ht := taylor_isLittleO (convex_ball (0 : ℝ) ε) hs0 (hfU.mono hsU)
  rw [nhdsWithin_eq_nhds.mpr hsnhds] at ht
  change (fun r => f r - taylorWithinEval f 2 s 0 r) =o[𝓝 0] (fun r : ℝ => (r - 0) ^ 2) at ht
  simpa only [hp, sub_zero] using ht

/-- The gradient defect has no contribution from the second derivative of the path. -/
theorem gradient_defect_second_order (g : E → E) (hg : ContDiffAt ℝ 2 g 0)
    (hg0 : g 0 = 0) (e : ℝ → E) (he : ContDiffAt ℝ 2 e 0) (he0 : e 0 = 0)
    (a : E) (ha : HasDerivAt e a 0) :
    (fun r => (g (e r) - fderiv ℝ g 0 (e r)) -
      r ^ 2 • ((1 / 2 : ℝ) • (fderiv ℝ (fderiv ℝ g) 0 a) a))
      =o[𝓝 0] (fun r : ℝ => r ^ 2) := by
  let A := fderiv ℝ g 0
  let B := fderiv ℝ (fderiv ℝ g) 0
  let F : ℝ → E := fun r => g (e r) - A (e r)
  have hFfun : (g ∘ e - A ∘ e) = F := by funext r; rfl
  have hgder : HasFDerivAt g A 0 := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hgc : ContDiffAt ℝ 2 (fun r => g (e r)) 0 := by
    have hg' : ContDiffAt ℝ 2 g (e 0) := by rw [he0]; exact hg
    exact hg'.comp 0 he
  have hFc : ContDiffAt ℝ 2 F 0 := hgc.sub (he.continuousLinearMap_comp A)
  have hF0 : F 0 = 0 := by simp [F, he0, hg0]
  have hF1 : deriv F 0 = 0 := by
    have hc := hgder.comp_hasDerivAt_of_eq 0 ha he0.symm
    have hl := A.hasFDerivAt.comp_hasDerivAt 0 ha
    have hh := hc.sub hl
    rw [hFfun] at hh
    simpa only [sub_self] using hh.deriv
  have hB : ContDiffAt ℝ 1 (fderiv ℝ g) 0 := hg.fderiv_right (by norm_num)
  have hq : HasDerivAt (fun r => fderiv ℝ g (e r) - A) (B a) 0 := by
    have hh := (hB.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq
      0 ha he0.symm
    simpa only [B, Function.comp_def] using hh.sub_const A
  have hde : ContDiffAt ℝ 1 (deriv e) 0 := he.derivWithin (by norm_num)
  have hprod := hq.clm_apply (hde.differentiableAt (by norm_num)).hasDerivAt
  have hderEq : deriv F =ᶠ[𝓝 0] (fun r => (fderiv ℝ g (e r) - A) (deriv e r)) := by
    have hge : ∀ᶠ r in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 g (e r) := by
      have hlim : Tendsto e (𝓝 0) (𝓝 (0 : E)) := by simpa only [he0] using he.continuousAt.tendsto
      exact hlim.eventually (hg.eventually (by norm_num))
    filter_upwards [hge, he.eventually (by norm_num)] with r hgr her
    have hc := (hgr.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt r
      (her.differentiableAt (by norm_num)).hasDerivAt
    have hl := A.hasFDerivAt.comp_hasDerivAt r
      (her.differentiableAt (by norm_num)).hasDerivAt
    have hh := hc.sub hl
    rw [hFfun] at hh
    simpa only [sub_apply] using hh.deriv
  have hF2 : deriv (deriv F) 0 = (B a) a := by
    have hh := hprod.congr_of_eventuallyEq hderEq
    simpa only [he0, A, ha.deriv, sub_self, zero_apply, add_zero] using hh.deriv
  have ht := second_order_taylor F hFc
  simpa only [hF0, hF1, hF2, zero_add, smul_zero, add_zero, F, A, B] using ht

end Perturbations

namespace TwoTerm
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The matrix of the actual derivative of the gradient map at the stationary point. -/
def gradientLinearization (g : (d → ℝ) → d → ℝ) : Matrix d d ℝ :=
  LinearMap.toMatrix' (fderiv ℝ g 0).toLinearMap

@[simp] theorem gradientLinearization_mulVec (g : (d → ℝ) → d → ℝ) (v : d → ℝ) :
    (gradientLinearization g).mulVec v = fderiv ℝ g 0 v := by
  exact LinearMap.toMatrix'_mulVec _ v

omit [Fintype d] [DecidableEq d] in
theorem nonlinearError_zero (S : TwoTerm) (g : (d → ℝ) → d → ℝ) (hg0 : g 0 = 0)
    (n : ℕ) : S.nonlinearError g 0 n = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [nonlinearError, hg0]
  | more n ih0 ih1 => simp [nonlinearError, hg0, ih0, ih1]

omit [DecidableEq d] in
theorem nonlinearError_contDiffAt (S : TwoTerm) (g : (d → ℝ) → d → ℝ)
    (hg : ContDiffAt ℝ 2 g 0) (hg0 : g 0 = 0) (u : d → ℝ) (n : ℕ) :
    ContDiffAt ℝ 2 (fun r : ℝ => S.nonlinearError g (r • u) n) 0 := by
  have hzero (s : ℕ) : S.nonlinearError g ((0 : ℝ) • u) s = 0 := by
    simpa using S.nonlinearError_zero g hg0 s
  induction n using Nat.twoStepInduction with
  | zero => simpa only [nonlinearError, id_eq] using
      (contDiffAt_id : ContDiffAt ℝ 2 (fun r : ℝ => r) 0).smul_const u
  | one =>
    have hi : ContDiffAt ℝ 2 (fun r : ℝ => r • u) 0 :=
      (contDiffAt_id : ContDiffAt ℝ 2 (fun r : ℝ => r) 0).smul_const u
    have hc : ContDiffAt ℝ 2 (fun r : ℝ => g (r • u)) 0 := by
      have hg' : ContDiffAt ℝ 2 g ((0 : ℝ) • u) := by simpa using hg
      exact hg'.comp 0 hi
    simpa only [nonlinearError, Pi.sub_apply] using hi.sub (hc.const_smul (S.gamma 0))
  | more n ih0 ih1 =>
    have hc : ContDiffAt ℝ 2 (fun r : ℝ => g (S.nonlinearError g (r • u) (n + 1))) 0 := by
      have hg' : ContDiffAt ℝ 2 g (S.nonlinearError g ((0 : ℝ) • u) (n + 1)) := by
        simpa only [hzero] using hg
      exact hg'.comp 0 ih1
    simpa only [nonlinearError, Pi.sub_apply, Pi.add_apply] using
      ((ih1.const_smul (S.a (n + 1))).add (ih0.const_smul (S.b (n + 1)))).sub
        (hc.const_smul (S.gamma (n + 1)))

theorem nonlinearError_hasDerivAt (S : TwoTerm) (g : (d → ℝ) → d → ℝ)
    (hg : ContDiffAt ℝ 2 g 0) (hg0 : g 0 = 0) (u : d → ℝ) (n : ℕ) :
    HasDerivAt (fun r : ℝ => S.nonlinearError g (r • u) n)
      (S.quadraticError (gradientLinearization g) u n) 0 := by
  have hgder := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hzero (s : ℕ) : S.nonlinearError g ((0 : ℝ) • u) s = 0 := by
    simpa using S.nonlinearError_zero g hg0 s
  have hu : HasDerivAt (fun r : ℝ => r • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  induction n using Nat.twoStepInduction with
  | zero => exact hu
  | one =>
    have hc := hgder.comp_hasDerivAt_of_eq 0 hu (by simp)
    have hh := hu.sub (hc.const_smul (S.gamma 0))
    have hfun : ((fun r : ℝ => r • u) - S.gamma 0 • (g ∘ fun r : ℝ => r • u)) =
        (fun r : ℝ => S.nonlinearError g (r • u) 1) := by funext r; rfl
    rw [hfun] at hh
    simpa only [quadraticError, gradientLinearization_mulVec] using hh
  | more n ih0 ih1 =>
    have hc := hgder.comp_hasDerivAt_of_eq 0 ih1 (hzero (n + 1)).symm
    have hh := ((ih1.const_smul (S.a (n + 1))).add (ih0.const_smul (S.b (n + 1)))).sub
      (hc.const_smul (S.gamma (n + 1)))
    have hfun : ((S.a (n + 1) • fun r : ℝ => S.nonlinearError g (r • u) (n + 1)) +
        (S.b (n + 1) • fun r : ℝ => S.nonlinearError g (r • u) n) -
        S.gamma (n + 1) • (g ∘ fun r : ℝ => S.nonlinearError g (r • u) (n + 1))) =
        (fun r : ℝ => S.nonlinearError g (r • u) (n + 2)) := by funext r; rfl
    rw [hfun] at hh
    simpa only [quadraticError, gradientLinearization_mulVec] using hh

theorem quadraticError_smul (S : TwoTerm) (H : Matrix d d ℝ) (u : d → ℝ)
    (r : ℝ) (N : ℕ) : S.quadraticError H (r • u) N = r • S.quadraticError H u N := by
  rw [S.quadraticError_eq_transfer, S.quadraticError_eq_transfer, Matrix.mulVec_smul]

/-- The second-order terminal coefficient, defined using the actual second derivative of `g`. -/
def quadraticCorrection (S : TwoTerm) (g : (d → ℝ) → d → ℝ) (u : d → ℝ) (N : ℕ) : d → ℝ :=
  ∑ s ∈ Finset.range N, -(S.gamma s) • S.forcingTail (gradientLinearization g) N s
    ((1 / 2 : ℝ) • (fderiv ℝ (fderiv ℝ g) 0
      (S.quadraticError (gradientLinearization g) u s))
        (S.quadraticError (gradientLinearization g) u s))

/-- The explicit Hessian-tensor forcing formula for the quadratic correction. -/
theorem quadraticCorrection_eq_sum (S : TwoTerm) (g : (d → ℝ) → d → ℝ)
    (u : d → ℝ) (N : ℕ) :
    S.quadraticCorrection g u N = -(1 / 2 : ℝ) •
      ∑ s ∈ Finset.range N, S.gamma s • S.forcingTail (gradientLinearization g) N s
        ((fderiv ℝ (fderiv ℝ g) 0 (S.quadraticError (gradientLinearization g) u s))
          (S.quadraticError (gradientLinearization g) u s)) := by
  simp only [quadraticCorrection, Finset.smul_sum, map_smul, smul_smul]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  ring

/-- The finite nonlinear run has the derived second-order expansion at every horizon. -/
theorem nonlinearError_second_order (S : TwoTerm) (g : (d → ℝ) → d → ℝ)
    (hg : ContDiffAt ℝ 2 g 0) (hg0 : g 0 = 0) (u : d → ℝ) (N : ℕ) :
    (fun r : ℝ => S.nonlinearError g (r • u) N -
      (r • S.quadraticError (gradientLinearization g) u N +
        r ^ 2 • S.quadraticCorrection g u N)) =o[𝓝 0] (fun r : ℝ => r ^ 2) := by
  let H := gradientLinearization g
  let e (s : ℕ) (r : ℝ) := S.nonlinearError g (r • u) s
  let a (s : ℕ) := S.quadraticError H u s
  let B := fderiv ℝ (fderiv ℝ g) 0
  let R (s : ℕ) (r : ℝ) := (g (e s r) - H.mulVec (e s r)) -
    r ^ 2 • ((1 / 2 : ℝ) • (B (a s)) (a s))
  let L (s : ℕ) : (d → ℝ) →L[ℝ] (d → ℝ) :=
    -(S.gamma s) • (S.forcingTail H N s).toContinuousLinearMap
  have hR (s : ℕ) : R s =o[𝓝 0] (fun r : ℝ => r ^ 2) := by
    have hzero : e s 0 = 0 := by simpa only [e, zero_smul] using S.nonlinearError_zero g hg0 s
    have hh := Perturbations.gradient_defect_second_order g hg hg0 (e s)
      (S.nonlinearError_contDiffAt g hg hg0 u s) hzero (a s)
      (S.nonlinearError_hasDerivAt g hg hg0 u s)
    simpa only [R, H, gradientLinearization_mulVec, B] using hh
  have hL (s : ℕ) : (fun r => L s (R s r)) =o[𝓝 0] (fun r : ℝ => r ^ 2) :=
    ((L s).isBigO_comp (R s) (𝓝 0)).trans_isLittleO (hR s)
  have hsum : (∑ s ∈ Finset.range N, fun r => L s (R s r)) =o[𝓝 0]
      (fun r : ℝ => r ^ 2) := IsLittleO.sum (fun s _ => hL s)
  have hcoeff : (∑ s ∈ Finset.range N, L s ((1 / 2 : ℝ) • (B (a s)) (a s))) =
      S.quadraticCorrection g u N := rfl
  have hcoeff' : (1 / 2 : ℝ) • (∑ s ∈ Finset.range N, L s ((B (a s)) (a s))) =
      S.quadraticCorrection g u N := by
    simpa only [map_smul, ← Finset.smul_sum] using hcoeff
  have hforcing (r : ℝ) : (∑ s ∈ Finset.range N,
      L s (g (e s r) - H.mulVec (e s r))) =
      ∑ s ∈ Finset.range N, S.forcingTail H N s
        (-(S.gamma s • (g (e s r) - H.mulVec (e s r)))) := by
    apply Finset.sum_congr rfl
    intro s _
    simp only [L, smul_apply, LinearMap.coe_toContinuousLinearMap', map_neg, map_smul, neg_smul]
  convert hsum using 1
  funext r
  simp only [Finset.sum_apply, R, map_sub, map_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
  have hforcing' := hforcing r
  simp only [map_sub, Finset.sum_sub_distrib] at hforcing'
  rw [hcoeff', hforcing', S.nonlinearError_eq_quadratic_add_forcing g H (r • u) N,
    S.quadraticError_smul]
  change _ = (∑ s ∈ Finset.range N, S.forcingTail H N s
    (-(S.gamma s • (g (S.nonlinearError g (r • u) s) -
      H.mulVec (S.nonlinearError g (r • u) s))))) - r ^ 2 • S.quadraticCorrection g u N
  abel

theorem quadraticError_neg (S : TwoTerm) (H : Matrix d d ℝ) (u : d → ℝ) (N : ℕ) :
    S.quadraticError H (-u) N = -S.quadraticError H u N := by
  simpa only [neg_one_smul] using S.quadraticError_smul H u (-1) N

/-- The first variation is odd in the initial direction; the quadratic correction is even. -/
theorem quadraticCorrection_neg (S : TwoTerm) (g : (d → ℝ) → d → ℝ)
    (u : d → ℝ) (N : ℕ) : S.quadraticCorrection g (-u) N = S.quadraticCorrection g u N := by
  simp only [quadraticCorrection, S.quadraticError_neg, map_neg, neg_apply, neg_neg]

/-- The radial formula follows from the actual nonlinear expansion in Euclidean norm. -/
theorem nonlinearError_radialNorm (S : TwoTerm) (g : (d → ℝ) → d → ℝ)
    (hg : ContDiffAt ℝ 2 g 0) (hg0 : g 0 = 0) (u : d → ℝ) (N : ℕ) :
    let a := WithLp.toLp 2 (S.quadraticError (gradientLinearization g) u N)
    let b := WithLp.toLp 2 (S.quadraticCorrection g u N)
    HasDerivWithinAt (fun r : ℝ => ‖Perturbations.radialVector
      (fun t : ℝ => WithLp.toLp 2 (S.nonlinearError g (t • u) N)) a r‖)
      (Perturbations.radialSlope a b) (Ioi 0) 0 := by
  let T : (d → ℝ) →L[ℝ] EuclideanSpace ℝ d :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)).symm.toContinuousLinearMap
  have he := S.nonlinearError_second_order g hg hg0 u N
  have ht := (T.isBigO_comp _ (𝓝 0)).trans_isLittleO he
  have hexp : (fun r : ℝ => T (S.nonlinearError g (r • u) N) -
      (r • T (S.quadraticError (gradientLinearization g) u N) +
        r ^ 2 • T (S.quadraticCorrection g u N))) =o[𝓝 0] (fun r : ℝ => r ^ 2) := by
    simpa only [map_sub, map_add, map_smul] using ht
  exact Perturbations.radialNorm_hasDerivWithinAt _ _ _ hexp

end TwoTerm

namespace Perturbations

/-- A C³ objective has a C² gradient in the Hilbert-space sense. -/
theorem objective_gradient_contDiffAt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (hf : ContDiffAt ℝ 3 f 0) :
    ContDiffAt ℝ 2 (gradient f) 0 := by
  have hd : ContDiffAt ℝ 2 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  exact hd.continuousLinearMap_comp
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Passing to the article's finite coordinate representation preserves this regularity. -/
theorem objective_gradientCoordinates_contDiffAt {d : Type*} [Fintype d]
    (f : EuclideanSpace ℝ d → ℝ) (hf : ContDiffAt ℝ 3 f 0) :
    ContDiffAt ℝ 2 (Nonlinear.gradientCoordinates (gradient f)) 0 := by
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)
  have hg := objective_gradient_contDiffAt f hf
  have hpre : ContDiffAt ℝ 2 (fun v : d → ℝ => gradient f (T.symm v)) 0 := by
    have hg' : ContDiffAt ℝ 2 (gradient f) (T.symm (0 : d → ℝ)) := by simpa using hg
    exact hg'.comp 0 T.symm.contDiff.contDiffAt
  exact hpre.continuousLinearMap_comp T.toContinuousLinearMap

end Perturbations

namespace TwoTerm
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The C³ objective version requires only stationarity, not a postulated expansion. -/
theorem objectiveError_second_order (S : TwoTerm) (f : EuclideanSpace ℝ d → ℝ)
    (hf : ContDiffAt ℝ 3 f 0) (hstationary : gradient f 0 = 0) (u : d → ℝ) (N : ℕ) :
    let g := Nonlinear.gradientCoordinates (gradient f)
    (fun r : ℝ => S.nonlinearError g (r • u) N -
      (r • S.quadraticError (gradientLinearization g) u N +
        r ^ 2 • S.quadraticCorrection g u N)) =o[𝓝 0] (fun r : ℝ => r ^ 2) := by
  apply S.nonlinearError_second_order _
    (Perturbations.objective_gradientCoordinates_contDiffAt f hf)
  simp [Nonlinear.gradientCoordinates, hstationary]

theorem objectiveError_radialNorm (S : TwoTerm) (f : EuclideanSpace ℝ d → ℝ)
    (hf : ContDiffAt ℝ 3 f 0) (hstationary : gradient f 0 = 0) (u : d → ℝ) (N : ℕ) :
    let g := Nonlinear.gradientCoordinates (gradient f)
    let a := WithLp.toLp 2 (S.quadraticError (gradientLinearization g) u N)
    let b := WithLp.toLp 2 (S.quadraticCorrection g u N)
    HasDerivWithinAt (fun r : ℝ => ‖Perturbations.radialVector
      (fun t : ℝ => WithLp.toLp 2 (S.nonlinearError g (t • u) N)) a r‖)
      (Perturbations.radialSlope a b) (Ioi 0) 0 := by
  apply S.nonlinearError_radialNorm _
    (Perturbations.objective_gradientCoordinates_contDiffAt f hf)
  simp [Nonlinear.gradientCoordinates, hstationary]

end TwoTerm
end
end chebyshev1
