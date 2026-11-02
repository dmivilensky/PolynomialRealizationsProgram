import krylov.XR.ContractiveFlag

/-!
Article: main_krylov, prop:status, exact flag-conditioning equality.
Use: characterize kappa_flat=1 by the original correction-base conjugacy.
Source: the proved contractive-idempotent theorem and exact positive-root
transport; commutation with every chronological prefix forces a diagonal Gram.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {p : ℕ}

/-- A contractive actual transported flag forces the genuine correction
base to commute with that chronological prefix. Article: prop:status. -/
theorem transportedFlag_commute_of_contractive (G : Matrix (Fin p) (Fin p) ℝ)
    (hG : G.PosDef) (l : ℕ) (hn : ‖transportedFlag G l‖≤1) :
    Commute G (prefixProjection p l) := by
  have hs := contractive_idempotent_isSymm (transportedFlag G l) hn
    (transportedFlag_idempotent G hG l)
  have hh := congrArg (fun X=>metricRoot G*X*metricRoot G) hs.eq
  have hleft : metricRoot G*(transportedFlag G l)ᵀ*metricRoot G=G*prefixProjection p l := by
    simp only [transportedFlag,transpose_mul,transpose_nonsing_inv,
      (metricRoot_isSymm G).eq,(prefixProjection_isSymm p l).eq]
    calc
      _ = (metricRoot G*metricRoot G)*prefixProjection p l*((metricRoot G)⁻¹*metricRoot G) := by noncomm_ring
      _ = _ := by rw [metricRoot_square G hG,nonsing_inv_mul _ (metricRoot_det_unit G hG),mul_one]
  have hright : metricRoot G*transportedFlag G l*metricRoot G=prefixProjection p l*G := by
    unfold transportedFlag
    calc
      _ = (metricRoot G*(metricRoot G)⁻¹)*prefixProjection p l*(metricRoot G*metricRoot G) := by noncomm_ring
      _ = _ := by rw [mul_nonsing_inv _ (metricRoot_det_unit G hG),one_mul,metricRoot_square G hG]
  rw [hleft,hright] at hh
  exact hh

/-- Exactly the genuinely conjugate windows have unit actual flag
conditioning, including dimensions zero and one. Article: prop:status. -/
theorem flagCondition_eq_one_iff (G : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef) :
    flagCondition G=1 ↔ G=diagonal (fun i=>G i i) := by
  constructor
  · intro hk
    have hcomm (l : ℕ) (hl : l<p) : Commute G (prefixProjection p l) :=
      transportedFlag_commute_of_contractive G hG l ((transportedFlag_norm_le G l hl).trans_eq hk)
    have hz (i j : Fin p) (hne : i≠j) : G i j=0 := by
      by_cases hij : i.val < j.val
      · have hh := congrFun (congrFun (hcomm i.val i.isLt).eq i) j
        have hji : ¬j.val ≤ i.val := by omega
        simp only [prefixProjection,mul_diagonal,diagonal_mul] at hh
        change G i j*(if j.val ≤ i.val then 1 else 0)=
          (if i.val ≤ i.val then 1 else 0)*G i j at hh
        simpa only [ite_eq_right hji,ite_eq_left (le_refl i.val),mul_zero,one_mul] using hh.symm
      · have hji : j.val < i.val := by have hn := Fin.val_injective.ne hne; omega
        have hh := congrFun (congrFun (hcomm j.val j.isLt).eq i) j
        have hij' : ¬i.val ≤ j.val := by omega
        simp only [prefixProjection,mul_diagonal,diagonal_mul] at hh
        change G i j*(if j.val ≤ j.val then 1 else 0)=
          (if i.val ≤ j.val then 1 else 0)*G i j at hh
        simpa only [ite_eq_left (le_refl j.val),ite_eq_right hij',mul_one,zero_mul] using hh
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [diagonal_apply_eq]
    · rw [hz i j hij]
      simp only [diagonal_apply_ne _ hij]
  · intro hd
    calc
      _ = flagCondition (diagonal (fun i=>G i i)) := congrArg flagCondition hd
      _ = 1 := flagCondition_diagonal _ (hd ▸ hG)

end
end krylov.XR
