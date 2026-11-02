import krylov.Correction.RFCSFieldRegularity

/-!
Article: main_krylov, thm:RFCS, genuine bounded finite-probe families.
Use: Bound actual reference CG search lengths and their reciprocals uniformly
on compact full-active families, prove positive actual perturbed lengths and
control the source's true relative last-probe error.
Source: genuine analytic search fields, real CG positivity, compact value
and first-order tubes, and exact positive scalar inequalities.
-/

namespace krylov.Correction
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Stability
variable {k : ℕ}

/-- All genuine active CG reference search lengths and their reciprocals have one positive uniform bound on a compact full-active initial-gradient family.
Use: Convert the original bounded relative probe-length rule into a common bound on real finite probe displacements.
Article: main_krylov, thm:RFCS, actual bounded-probe family and positive search lengths.
Proof: The actual positive CG lengths have jointly analytic genuine search fields. Apply the proved compact value tube to the finite product of each length and its reciprocal.
-/
theorem compact_rfcs_reference_length_bounds (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) :
    ∃ M : ℝ, 0<M ∧ ∀ g∈K, ∀ i<k+1,
      0<CG.length (cgOperator base) g i ∧ (CG.length (cgOperator base) g i)⁻¹≤M ∧
        CG.length (cgOperator base) g i≤M := by
  have hpos g (hg : g∈K) i (hi : i<k+1) : 0<CG.length (cgOperator base) g i := by
    have hQ := cgOperator_positive base hb
    exact (CG.invariant_line_pos _ hQ.2 g i
      (CG.invariant _ hQ.1 hQ.2 g i (fun j hj => cg_nonstagnation base hb g j (hj.trans_le (hi.le.trans (hN g hg)))))
      (cg_nonstagnation base hb g i (hi.trans_le (hN g hg)))).2.1
  let f := fun z => fun i : Fin (k+1) => (rfcsDirectAlpha base i.val z,(rfcsDirectAlpha base i.val z)⁻¹)
  have hf g (hg : g∈K) : AnalyticAt ℝ f (g,0) := by
    apply AnalyticAt.pi
    intro i
    have ha := (rfcs_direct_search_fields_analytic base hb g (hN g hg) i.val i.isLt).1
    have hn : rfcsDirectAlpha base i.val (g,0)≠0 := by
      rw [(rfcs_direct_alpha_reference base hb g i.val).1]
      exact (hpos g hg i.val i.isLt).ne'
    exact ha.prod (ha.inv hn)
  obtain ⟨δ,M,_,hM,hbound⟩ := compact_reference_value_tube f K hK hf
  refine ⟨M,hM,?_⟩
  intro g hg i hi
  have hb' := hbound g hg 0 0 (by simp only [Prod.norm_mk,norm_zero,max_self]; linarith)
  rw [add_zero] at hb'
  have he := (norm_le_pi_norm (f (g,0)) (⟨i,hi⟩ : Fin (k+1))).trans hb'
  have ha := (norm_fst_le (f (g,0) ⟨i,hi⟩)).trans he
  have hinv := (norm_snd_le (f (g,0) ⟨i,hi⟩)).trans he
  dsimp only [f] at ha hinv
  rw [(rfcs_direct_alpha_reference base hb g i).1,Real.norm_eq_abs,abs_of_pos (hpos g hg i hi)] at ha
  rw [(rfcs_direct_alpha_reference base hb g i).1,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hpos g hg i hi))] at hinv
  exact ⟨hpos g hg i hi,hinv,ha⟩


/-- One genuine compact source tube makes every actual RFC-S search length positive and between one half and three halves of its true original CG reference length.
Use: Discharge the real search-length domain and uniformly compare the actual and reference finite-probe scales.
Article: main_krylov, thm:RFCS, actual bounded-probe family and positive search lengths.
Proof: Use the common first-order actual search-length bound and the proved compact reciprocal reference bound, choosing the source radius before every reference and iteration.
-/
theorem compact_rfcs_relative_length_bounds (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) :
    ∃ δ : ℝ, 0<δ ∧ ∀ g∈K, ∀ v : EuclideanSpace ℝ (Fin (k+1)),
      ∀ Θ : RFCSOperatorParameters (k+1), ‖(v,Θ)‖≤δ → ∀ i<k+1,
      0<rfcsDirectAlpha base i (g+v,Θ) ∧
      CG.length (cgOperator base) g i/2≤rfcsDirectAlpha base i (g+v,Θ) ∧
      rfcsDirectAlpha base i (g+v,Θ)≤3*CG.length (cgOperator base) g i/2 := by
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_rfcs_search_field_changes base hb K hK hN
  obtain ⟨M,hM,href⟩ := compact_rfcs_reference_length_bounds base hb K hK hN
  refine ⟨min δ (2*C*M)⁻¹,lt_min hδ (inv_pos.mpr (by positivity)),?_⟩
  intro g hg v Θ hΘ i hi
  obtain ⟨ha,hinv,_⟩ := href g hg i hi
  have hlower : M⁻¹≤CG.length (cgOperator base) g i := (inv_le_comm₀ hM ha).mpr hinv
  have herr : |rfcsDirectAlpha base i (g+v,Θ)-CG.length (cgOperator base) g i|≤CG.length (cgOperator base) g i/2 := by
    calc
      _ ≤ C*‖(v,Θ)‖ := (hbound g hg v Θ (hΘ.trans (min_le_left _ _)) i hi).1
      _ ≤ C*(2*C*M)⁻¹ := mul_le_mul_of_nonneg_left (hΘ.trans (min_le_right _ _)) hC.le
      _ = M⁻¹/2 := by field_simp
      _ ≤ _ := by linarith
  have he := abs_le.mp herr
  exact ⟨by linarith,by linarith,by linarith⟩

/-- A positive finite probe bounded by its true CG reference length has uniformly bounded actual relative probe error whenever the genuine predicted length is at least half its reference value.
Use: Control the source factor |1-h/α| uniformly while preserving its actual value in the sharp nonlinear coefficient.
Article: main_krylov, thm:RFCS, actual bounded-probe family and positive search lengths.
Proof: The real length lower bound bounds the positive quotient h/α; apply the ordinary scalar absolute-value triangle inequality.
-/
theorem relative_probe_error_bound {α α₀ h Cp : ℝ} (hα₀ : 0<α₀) (hα : α₀/2≤α)
    (hh : 0<h) (hp : h≤Cp*α₀) : |1-h/α|≤1+2*Cp := by
  have hapos : 0<α := by linarith
  have hCp : 0<Cp := by nlinarith
  have hratio : h/α≤2*Cp := (div_le_iff₀ hapos).mpr (by nlinarith)
  have hratio₀ : 0≤h/α := (div_pos hh hapos).le
  have htriangle : |1-h/α|≤1+h/α := by
    have ha := abs_sub 1 (h/α)
    simpa only [abs_one,abs_of_nonneg hratio₀] using ha
  linarith

end
end krylov.Correction
