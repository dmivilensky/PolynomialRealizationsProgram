import nesterov.Slow.Factorization
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.LeftRight

/-! Regularity of the real root near one and of the deflated coefficients.
The implicit function theorem is applied to finite coefficient vectors, so
only the original right-sided coefficient germs enter the conclusion. -/
namespace nesterov.Slow
noncomputable section
open Polynomial Filter Set
open scoped Topology ContDiff

private def vectorEval (N : ℕ) (v : (Fin (N+1)→ℝ) × ℝ) : ℝ :=
  ∑ i : Fin (N+1),v.1 i*v.2^i.val

private theorem vectorEval_coeff {N : ℕ} (p : Polynomial ℝ) (hN : p.natDegree≤N) (z : ℝ) :
    vectorEval N ((fun i=>p.coeff i.val),z)=p.eval z := by
  unfold vectorEval
  dsimp only
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ=>p.coeff i*z^i) (N+1)).trans
    (Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hN (Nat.lt_succ_self N)) z).symm

/-- A simple real root is a smooth function of the finite coefficient vector.
Local uniqueness identifies it with every convergent root selection. -/
private theorem exists_smooth_root_map {N : ℕ} (p : Polynomial ℝ) (hN : p.natDegree≤N)
    (hp : p.eval 1=0) (hd : p.derivative.eval 1≠0) :
    ∃ ψ : (Fin (N+1)→ℝ)→ℝ,
      ContDiffAt ℝ ∞ ψ (fun i=>p.coeff i.val) ∧ ψ (fun i=>p.coeff i.val)=1 ∧
      ∀ᶠ v in 𝓝 ((fun i : Fin (N+1)=>p.coeff i.val),(1:ℝ)),
        vectorEval N v=0 ↔ ψ v.1=v.2 := by
  let a : Fin (N+1)→ℝ := fun i=>p.coeff i.val
  have hc : ContDiffAt ℝ ∞ (vectorEval N) (a,1) := by
    unfold vectorEval
    fun_prop
  have hi : HasFDerivAt (fun z : ℝ=>(a,z))
      (ContinuousLinearMap.inr ℝ (Fin (N+1)→ℝ) ℝ) 1 := by
    exact hasFDerivAt_prodMk_right a 1
  have he : (fun z : ℝ=>vectorEval N (a,z))=fun z=>p.eval z := by
    funext z
    exact vectorEval_coeff p hN z
  have hpartial := (hc.differentiableAt (by simp)).hasFDerivAt.comp 1 hi
  have hd' : HasFDerivAt (fun z : ℝ=>vectorEval N (a,z))
      (p.derivative.eval 1 • ContinuousLinearMap.id ℝ ℝ) 1 := by
    rw [he]
    convert (p.hasDerivAt (1:ℝ)).hasFDerivAt using 1
    ext
    simp [mul_comm]
  have hlin : fderiv ℝ (vectorEval N) (a,1) ∘L
      ContinuousLinearMap.inr ℝ (Fin (N+1)→ℝ) ℝ=
        p.derivative.eval 1 • ContinuousLinearMap.id ℝ ℝ := hpartial.unique hd'
  have hinv : (fderiv ℝ (vectorEval N) (a,1) ∘L
      ContinuousLinearMap.inr ℝ (Fin (N+1)→ℝ) ℝ).IsInvertible := by
    rw [hlin]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g:= (p.derivative.eval 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [hd]
    · ext
      simp [hd]
  refine ⟨hc.implicitFunction (by simp) hinv,hc.contDiffAt_implicitFunction (by simp) hinv,
    hc.implicitFunction_apply_self (by simp) hinv,?_⟩
  have hzero : vectorEval N (a,1)=0 := (vectorEval_coeff p hN 1).trans hp
  simpa only [hzero] using
    hc.eventually_apply_eq_iff_implicitFunction (by simp) hinv

private theorem divByMonic_coeff_ck {p : ℝ→Polynomial ℝ} {a : ℝ→ℝ} {N k : ℕ}
    (hdeg : ∀ ε,(p ε).natDegree≤N)
    (hp : ∀ j,ContDiffWithinAt ℝ k (fun ε=>(p ε).coeff j) (Ici 0) 0)
    (ha : ContDiffWithinAt ℝ k a (Ici 0) 0) (j : ℕ) :
    ContDiffWithinAt ℝ k (fun ε=>(p ε /ₘ (X-C (a ε))).coeff j) (Ici 0) 0 := by
  simp_rw [coeff_divByMonic_bounded _ _ (hdeg _) j]
  apply ContDiffWithinAt.sum
  intro i _
  exact (ha.pow _).mul (hp i)

namespace SecondOrderFamily
variable {θ y : ℝ} (F : SecondOrderFamily θ y)

/-- The near-one real root has exactly the coefficient family's original
one-sided smoothness, including continuity when k=0. -/
theorem beta_coeff_ck {k : ℕ} (hc : F.CoeffCk k) :
    ContDiffWithinAt ℝ k F.beta (Ici 0) 0 := by
  let P : ℝ→Polynomial ℝ := fun ε=>F.v ε /ₘ (X-C 1)
  have hdeg (ε : ℝ) : (P ε).natDegree≤F.memory := by
    dsimp only [P]
    rw [natDegree_divByMonic _ (monic_X_sub_C 1),natDegree_X_sub_C,F.v_natDegree]
    omega
  have hPcoeff (j : ℕ) : ContDiffWithinAt ℝ k (fun ε=>(P ε).coeff j) (Ici 0) 0 :=
    divByMonic_coeff_ck (fun ε=>(F.v_natDegree ε).le) hc.2 contDiffWithinAt_const j
  have hP0 : P 0=(X-C 1)*F.q0 := by
    change (F.method 0).recurrencePolynomial /ₘ (X-C 1)=(X-C 1)*F.q0
    rw [F.initial_factor,pow_two,mul_assoc,mul_divByMonic_cancel_left _ (monic_X_sub_C 1)]
  have hp0 : (P 0).eval 1=0 := by rw [hP0];simp
  have hd0 : (P 0).derivative.eval 1≠0 := by
    rw [hP0]
    simpa only [derivative_mul,derivative_sub,derivative_X,derivative_C,sub_zero,eval_add,
      eval_mul,eval_one,eval_sub,eval_X,eval_C,sub_self,one_mul,zero_mul,add_zero,F.q0_one] using
      div_ne_zero (by norm_num : (-1:ℝ)≠0) F.step_pos.ne'
  obtain ⟨ψ,hψ,hψ0,hlocal⟩ := exists_smooth_root_map (P 0) (hdeg 0) hp0 hd0
  let a : ℝ→(Fin (F.memory+1)→ℝ) := fun ε i=>(P ε).coeff i.val
  have ha : ContDiffWithinAt ℝ k a (Ici 0) 0 :=
    contDiffWithinAt_pi.mpr (fun i=>hPcoeff i.val)
  have hpair : Tendsto (fun ε=>(a ε,F.beta ε)) (𝓝[>] (0:ℝ)) (𝓝 (a 0,1)) := by
    exact ((ha.continuousWithinAt.tendsto).mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self)).prodMk_nhds F.beta_tendsto
  have hroot : ∀ᶠ ε in 𝓝[>] (0:ℝ),(P ε).eval (F.beta ε)=0 := by
    filter_upwards [F.factorization] with ε hε
    dsimp only [P]
    rw [hε,mul_assoc,mul_divByMonic_cancel_left _ (monic_X_sub_C 1)]
    simp
  have heq : F.beta=ᶠ[𝓝[>] (0:ℝ)] fun ε=>ψ (a ε) := by
    filter_upwards [hpair.eventually hlocal,hroot] with ε hε hr
    exact (hε.mp ((vectorEval_coeff (P ε) (hdeg ε) (F.beta ε)).trans hr)).symm
  have heq0 : F.beta 0=ψ (a 0) := F.beta_zero.trans hψ0.symm
  have heqclosed : F.beta=ᶠ[𝓝[≥] (0:ℝ)] fun ε=>ψ (a ε) := by
    change {ε : ℝ|F.beta ε=ψ (a ε)}∈𝓝[≥] (0:ℝ)
    rw [show Ici (0:ℝ)=insert 0 (Ioi 0) by
      ext x
      simp only [mem_Ici,mem_insert_iff,mem_Ioi]
      constructor
      · intro hx
        rcases eq_or_lt_of_le hx with hx|hx
        · exact Or.inl hx.symm
        · exact Or.inr hx
      · rintro (rfl|hx)
        · exact le_rfl
        · exact hx.le,
      mem_nhdsWithin_insert]
    exact ⟨heq0,heq⟩
  have hcomp : ContDiffWithinAt ℝ k (fun ε=>ψ (a ε)) (Ici 0) 0 :=
    (hψ.of_le (by simp)).comp_contDiffWithinAt 0 ha
  exact hcomp.congr_of_eventuallyEq heqclosed heq0

/-- All deflated coefficients retain the original Ck regularity. -/
theorem quotient_coeff_ck {k : ℕ} (hc : F.CoeffCk k) (j : ℕ) :
    ContDiffWithinAt ℝ k (fun ε=>(F.quotient ε).coeff j) (Ici 0) 0 := by
  apply divByMonic_coeff_ck (N:=F.memory)
  · intro ε
    rw [natDegree_divByMonic _ (monic_X_sub_C 1),natDegree_X_sub_C,F.v_natDegree]
    omega
  · intro i
    exact divByMonic_coeff_ck (fun ε=>(F.v_natDegree ε).le) hc.2 contDiffWithinAt_const i
  · exact F.beta_coeff_ck hc

end SecondOrderFamily

end
end nesterov.Slow
