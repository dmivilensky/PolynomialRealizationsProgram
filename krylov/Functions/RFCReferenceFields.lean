import krylov.Functions.FCReferenceFields
import krylov.Stability.AnalyticRFC
import krylov.Stability.CompactEventual
import krylov.Methods.HomogeneousRFC

/-!
Article: main_krylov, lem:cycle-transfer, compact ordinary RFC reference fields.
Use: a common actual neighborhood controls every direction, line step and
correction displacement in the genuine ordinary RFC executor. The correction
field is evaluated before its current correction operator can affect it.
Source: the proved ordinary RFC analytic induction and compact Taylor tube.
-/
namespace krylov.Functions
noncomputable section
open Set Filter Topology krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real line step preceding the actual RFC correction query.
Article: main_krylov, alg:fc, ordinary RFC. -/
def rfcOperatorLineStep (A B : ℕ → E →L[ℝ] E) (g : E) (i : ℕ) : E :=
  let H := methodRun (rfcMethod fullMemory 1) A B g i
  let d := (rfcMethod fullMemory 1).direction H
  lineLength H.gradient d (A i d) • d

/-- The real RFC correction displacement, read from its actual recorded step.
Article: main_krylov, alg:fc, ordinary RFC with one correction. -/
def rfcOperatorCorrection (A B : ℕ → E →L[ℝ] E) (g : E) (i : ℕ) : E :=
  probedStep (rfcMethod fullMemory 1) A B g i-rfcOperatorLineStep A B g i

/-- The genuine quadratic ordinary RFC correction vanishes.
Article: main_krylov, lem:consistent(a). -/
theorem rfcOperatorCorrection_reference (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (i : ℕ) : rfcOperatorCorrection (fun _=>Q) (fun _=>Q) g i=0 := by
  have hm : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<fullMemory k := fun _ _ hk=>hk
  unfold rfcOperatorCorrection rfcOperatorLineStep
  rw [(rfc_reference_pair fullMemory 1 Q hQ hpos g hm i).1]
  have hd := rfc_reference_direction fullMemory 1 Q hQ hpos g hm i
  change (rfcMethod fullMemory 1).direction (methodRun _ _ _ _ _)=_ at hd
  have hg := (rfcMethod_static fullMemory 1 Q hQ hpos g hm i).1
  change referenceStep Q g i-lineLength _ _ _ • _=0
  rw [hd,hg]
  exact sub_self _

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- One actual compact-reference tube controls ordinary RFC directions, total
steps, and its true correction queries. No bounds on the computed fields are
assumed. Article: main_krylov, lem:cycle-transfer.
Proof: derive analytic line quotients from genuine positive CG curvature;
combine them with the proved analytic ordinary RFC execution, then apply the
compact first-order theorem to their actual finite product. -/
theorem compact_rfc_reference_field_changes (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i<N, CG.gradient Q g i≠0) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ g∈K, ∀ v : E,
      ∀ Θ Ξ : Fin N → E →L[ℝ] E, ‖(v,(Θ,Ξ))‖≤δ → ∀ i<N,
      let A := fcFiniteOperatorPath Q N Θ
      let B := fcFiniteOperatorPath Q N Ξ
      ‖(rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) A B (g+v) i)-CG.direction Q g i‖≤C*‖(v,(Θ,Ξ))‖ ∧
      ‖probedStep (rfcMethod fullMemory 1) A B (g+v) i-referenceStep Q g i‖≤C*‖(v,(Θ,Ξ))‖ ∧
      ‖rfcOperatorCorrection A B (g+v) i‖≤C*‖(v,(Θ,Ξ))‖ := by
  let A := fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E)) => fcFiniteOperatorPath Q N z.2.1
  let B := fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E)) => fcFiniteOperatorPath Q N z.2.2
  let F := fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E)) => fun i : Fin N =>
    ((rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) (A z) (B z) z.1 i.val),
      (probedStep (rfcMethod fullMemory 1) (A z) (B z) z.1 i.val,rfcOperatorCorrection (A z) (B z) z.1 i.val))
  have hA i z : AnalyticAt ℝ (fun z=>A z i) z := by
    by_cases hi : i<N
    · simp only [A,fcFiniteOperatorPath,dite_eq_left hi]
      have hp : AnalyticAt ℝ (fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>z.2.1) z :=
        analyticAt_fst.comp analyticAt_snd
      exact analyticAt_const.add (((ContinuousLinearMap.proj (R:=ℝ)
        (φ:=fun _ : Fin N=>E →L[ℝ] E) ⟨i,hi⟩).analyticAt z.2.1).comp (f:=fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>z.2.1) hp)
    · simp only [A,fcFiniteOperatorPath,dite_eq_right hi]
      exact analyticAt_const
  have hB i z : AnalyticAt ℝ (fun z=>B z i) z := by
    by_cases hi : i<N
    · simp only [B,fcFiniteOperatorPath,dite_eq_left hi]
      have hp : AnalyticAt ℝ (fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>z.2.2) z :=
        analyticAt_snd.comp analyticAt_snd
      exact analyticAt_const.add (((ContinuousLinearMap.proj (R:=ℝ)
        (φ:=fun _ : Fin N=>E →L[ℝ] E) ⟨i,hi⟩).analyticAt z.2.2).comp (f:=fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>z.2.2) hp)
    · simp only [B,fcFiniteOperatorPath,dite_eq_right hi]
      exact analyticAt_const
  have hAz g : A (g,0)=fun _=>Q := fcFiniteOperatorPath_zero Q N
  have hBz g : B (g,0)=fun _=>Q := fcFiniteOperatorPath_zero Q N
  have hm g : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<fullMemory k := fun _ _ hk=>hk
  have hF g (hg : g∈K) : AnalyticAt ℝ F (g,0) := by
    have ht := quadraticRFC_prefix_analytic fullMemory 1 A B Prod.fst (g,0)
      (fun i=>hA i _) (fun i=>hB i _) analyticAt_fst Q (hAz g) (hBz g) hQ hpos (hm g) N (hpre g hg)
    apply AnalyticAt.pi
    intro i
    have hgrad := (quadraticRFC_prefix_analytic fullMemory 1 A B Prod.fst (g,0)
      (fun j=>hA j _) (fun j=>hB j _) analyticAt_fst Q (hAz g) (hBz g) hQ hpos (hm g) i.val
      (fun j hj=>hpre g hg j (hj.trans i.isLt))).1
    have hd := (ht.2 i.val i.isLt).1
    have hz := analytic_operator_apply (hA i.val _) hd
    have hdx := rfc_reference_direction fullMemory 1 Q hQ hpos g (hm g) i.val
    change windowDirection _ (methodRun _ _ _ _ _).gradient=_ at hdx
    have hcurv : inner ℝ ((rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) (A (g,0)) (B (g,0)) g i.val))
        (A (g,0) i.val ((rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) (A (g,0)) (B (g,0)) g i.val)))≠0 := by
      rw [hAz,hBz]
      change inner ℝ (windowDirection _ _) (Q (windowDirection _ _))≠0
      rw [hdx]
      exact (hpos _ (CG.invariant_line_pos Q hpos g i.val
        (CG.invariant Q hQ hpos g i.val (fun j hj=>hpre g hg j (hj.trans i.isLt)))
        (hpre g hg i.val i.isLt)).1).ne'
    have hline := ((analytic_inner hd hgrad).neg.div (analytic_inner hd hz) hcurv).smul hd
    exact hd.prod ((ht.2 i.val i.isLt).2.1.prod ((ht.2 i.val i.isLt).2.1.sub hline))
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_reference_full_first_order F K hK hF
  refine ⟨δ,C,hδ,hC,?_⟩
  intro g hg v Θ Ξ hsmall i hi
  have hb := (norm_le_pi_norm (F (g+v,(Θ,Ξ))-F (g,0)) (⟨i,hi⟩ : Fin N)).trans
    (hbound g hg v (Θ,Ξ) hsmall)
  have hd := (norm_fst_le ((F (g+v,(Θ,Ξ))-F (g,0)) ⟨i,hi⟩)).trans hb
  have hs := (norm_fst_le (((F (g+v,(Θ,Ξ))-F (g,0)) ⟨i,hi⟩).2)).trans ((norm_snd_le _).trans hb)
  have hu := (norm_snd_le (((F (g+v,(Θ,Ξ))-F (g,0)) ⟨i,hi⟩).2)).trans ((norm_snd_le _).trans hb)
  dsimp only [F,Pi.sub_apply,Prod.mk_sub_mk] at hd hs hu
  rw [hAz,hBz] at hd hs hu
  have hdx := rfc_reference_direction fullMemory 1 Q hQ hpos g (hm g) i
  change (rfcMethod fullMemory 1).direction (methodRun _ _ _ _ _)=_ at hdx
  rw [hdx] at hd
  rw [(rfc_reference_pair fullMemory 1 Q hQ hpos g (hm g) i).1] at hs
  rw [rfcOperatorCorrection_reference Q hQ hpos g i,sub_zero] at hu
  exact ⟨hd,hs,hu⟩
omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Every genuine search denominator and numerator is nonzero on one common
compact ordinary RFC input tube. Article: main_krylov, lem:cycle-transfer.
The domains follow from actual positive CG reference searches and continuity,
not from assuming that the nonlinear trajectory is a descent trajectory. -/
theorem compact_rfc_reference_search_domain (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i<N, CG.gradient Q g i≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ g∈K, ∀ v : E, ∀ Θ Ξ : Fin N → E →L[ℝ] E,
      ‖(v,(Θ,Ξ))‖≤δ → ∀ i<N,
      let A := fcFiniteOperatorPath Q N Θ
      let B := fcFiniteOperatorPath Q N Ξ
      let H := methodRun (rfcMethod fullMemory 1) A B (g+v) i
      let d := (rfcMethod fullMemory 1).direction H
      d≠0 ∧ lineLength H.gradient d (A i d)≠0 := by
  let A := fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E)) => fcFiniteOperatorPath Q N z.2.1
  let B := fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E)) => fcFiniteOperatorPath Q N z.2.2
  let D := fun z i => (rfcMethod fullMemory 1).direction
    (methodRun (rfcMethod fullMemory 1) (A z) (B z) z.1 i)
  let P := fun z => ∀ i : Fin N, D z i.val≠0 ∧
    lineLength (probedGradient (rfcMethod fullMemory 1) (A z) (B z) z.1 i.val) (D z i.val) (A z i.val (D z i.val))≠0
  have hA i z : AnalyticAt ℝ (fun z=>A z i) z := by
    by_cases hi : i<N
    · simp only [A,fcFiniteOperatorPath,dite_eq_left hi]
      have hp : AnalyticAt ℝ (fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>z.2.1) z :=
        analyticAt_fst.comp analyticAt_snd
      exact analyticAt_const.add (((ContinuousLinearMap.proj (R:=ℝ)
        (φ:=fun _ : Fin N=>E →L[ℝ] E) ⟨i,hi⟩).analyticAt z.2.1).comp
          (f:=fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>z.2.1) hp)
    · simp only [A,fcFiniteOperatorPath,dite_eq_right hi]
      exact analyticAt_const
  have hB i z : AnalyticAt ℝ (fun z=>B z i) z := by
    by_cases hi : i<N
    · simp only [B,fcFiniteOperatorPath,dite_eq_left hi]
      have hp : AnalyticAt ℝ (fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>z.2.2) z :=
        analyticAt_snd.comp analyticAt_snd
      exact analyticAt_const.add (((ContinuousLinearMap.proj (R:=ℝ)
        (φ:=fun _ : Fin N=>E →L[ℝ] E) ⟨i,hi⟩).analyticAt z.2.2).comp
          (f:=fun z : E × ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E))=>z.2.2) hp)
    · simp only [B,fcFiniteOperatorPath,dite_eq_right hi]
      exact analyticAt_const
  have hAz g : A (g,0)=fun _=>Q := fcFiniteOperatorPath_zero Q N
  have hBz g : B (g,0)=fun _=>Q := fcFiniteOperatorPath_zero Q N
  have hm g : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<fullMemory k := fun _ _ hk=>hk
  have hP g (hg : g∈K) : ∀ᶠ z in 𝓝 (g,0), P z := by
    rw [Filter.eventually_all]
    intro i
    have ht := quadraticRFC_prefix_analytic fullMemory 1 A B Prod.fst (g,0)
      (fun i=>hA i _) (fun i=>hB i _) analyticAt_fst Q (hAz g) (hBz g) hQ hpos (hm g) N (hpre g hg)
    have hgrad := (quadraticRFC_prefix_analytic fullMemory 1 A B Prod.fst (g,0)
      (fun j=>hA j _) (fun j=>hB j _) analyticAt_fst Q (hAz g) (hBz g) hQ hpos (hm g) i.val
      (fun j hj=>hpre g hg j (hj.trans i.isLt))).1
    have hd := (ht.2 i.val i.isLt).1
    have hz := analytic_operator_apply (hA i.val _) hd
    have hdx := rfc_reference_direction fullMemory 1 Q hQ hpos g (hm g) i.val
    change (rfcMethod fullMemory 1).direction (methodRun _ _ _ _ _)=_ at hdx
    have hgx := (rfcMethod_static fullMemory 1 Q hQ hpos g (hm g) i.val).1
    have hcg := CG.invariant_line_pos Q hpos g i.val
      (CG.invariant Q hQ hpos g i.val (fun j hj=>hpre g hg j (hj.trans i.isLt)))
      (hpre g hg i.val i.isLt)
    have hnum : inner ℝ (D (g,0) i.val)
        (probedGradient (rfcMethod fullMemory 1) (A (g,0)) (B (g,0)) g i.val)≠0 := by
      dsimp only [D]
      rw [hAz,hBz,hdx]
      change inner ℝ (CG.direction Q g i.val) (methodRun _ _ _ _ _).gradient≠0
      rw [hgx]
      have hlen := hcg.2.1.ne'
      exact neg_ne_zero.mp (div_ne_zero_iff.mp hlen).1
    have hcurv : inner ℝ (D (g,0) i.val) (A (g,0) i.val (D (g,0) i.val))≠0 := by
      dsimp only [D]
      rw [hAz,hBz,hdx]
      exact (hpos _ hcg.1).ne'
    have hn := (analytic_inner hd hgrad).continuousAt.eventually_ne hnum
    have hc := (analytic_inner hd hz).continuousAt.eventually_ne hcurv
    filter_upwards [hn,hc] with z hn hc
    refine ⟨?_,div_ne_zero (neg_ne_zero.mpr hn) hc⟩
    intro he
    change inner ℝ (D z i.val) _≠0 at hn
    exact hn (by simp only [he,inner_zero_left])
  obtain ⟨δ,hδ,hbound⟩ := compact_reference_eventual_tube P K hK hP
  refine ⟨δ,hδ,?_⟩
  intro g hg v Θ Ξ hsmall i hi
  exact hbound g hg v (Θ,Ξ) hsmall ⟨i,hi⟩

end
end krylov.Functions
