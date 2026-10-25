import polyak.CertifiedExamples.Plateaus.SymbolSemantics
import polyak.Farey.Examples.FloorCertificate
import polyak.ModeLocking.Analysis.JetCover

/-! A finite exact cover proves a global polynomial sign. A curvature cell
contains its marked genuine double zero; Taylor's theorem covers every real
point of that cell. No grid sampling is a mathematical premise. -/
namespace polyak.CertifiedExamples.Plateaus
open LeanCert.Core LeanCert.Engine

abbrev CoverCell (d:ℕ) := IntervalRat×Option (Fin d)

def cellCheck {r d:ℕ} (X:Fin 3→IntervalRat) (lam:Fin r→IntervalRat)
    (C:Fin d→IntervalRat) (P0 P2:Fin (r*4)→QPoly) (D:ℕ) (cell:CoverCell d) : Bool :=
  match cell.2 with
  | none=>Bernstein.check P0 (weightBoxes X lam) cell.1 D
  | some i=>Bernstein.check P2 (weightBoxes X lam) cell.1 D &&
      decide (cell.1.lo≤(C i).lo ∧ (C i).hi≤cell.1.hi)

def coverCheck {r d:ℕ} (X:Fin 3→IntervalRat) (lam:Fin r→IntervalRat)
    (C:Fin d→IntervalRat) (P0 P2:Fin (r*4)→QPoly) (D:ℕ) (cells:List (CoverCell d)) : Bool :=
  Farey.Examples.intervalCoverCheck (-1) (cells.map Prod.fst) &&
    decide (∀cell∈cells,cellCheck X lam C P0 P2 D cell=true) &&
    decide (∀i:Fin d,∃cell∈cells,cell.2=some i)

noncomputable section
open General Levels Polynomial Set

theorem family0_negative {r:ℕ} (q:Tuning) (n:Fin r→ℤ) (lam:Fin r→ℝ)
    (X:Fin 3→IntervalRat) (B:Fin r→IntervalRat) (P:Fin (r*4)→QPoly)
    (hid:familyIdentityCheck n 0 P=true) (I:IntervalRat) (D:ℕ)
    (hc:Bernstein.check P (weightBoxes X B) I D=true)
    (hX:∀i,coefficientVector q i∈X i) (hlam:∀j,lam j∈B j) {x:ℝ} (hx:x∈I) :
    indexedSymbol q n lam x<0 := by
  have h:=Bernstein.negative P (weightBoxes X B) I D hc
    (weightValues_mem (coefficientVector q) lam X B hX hlam) hx
  have he : weightedFunction (weightValues (coefficientVector q) lam) P=
      weightedFunction (weightValues (coefficientVector q) lam) (sourceFamily n 0) := by
    funext c
    unfold weightedFunction
    apply Finset.sum_congr rfl
    intro i _
    rw [familyIdentity_sound n 0 P hid i]
  change weightedFunction _ P x<0 at h
  rw [he,sourceFamily_zero] at h
  exact h

theorem family2_negative {r:ℕ} (q:Tuning) (n:Fin r→ℤ) (lam:Fin r→ℝ)
    (X:Fin 3→IntervalRat) (B:Fin r→IntervalRat) (P:Fin (r*4)→QPoly)
    (hid:familyIdentityCheck n 2 P=true) (I:IntervalRat) (D:ℕ)
    (hc:Bernstein.check P (weightBoxes X B) I D=true)
    (hX:∀i,coefficientVector q i∈X i) (hlam:∀j,lam j∈B j) {x:ℝ} (hx:x∈I) :
    deriv^[2] (indexedSymbol q n lam) x<0 := by
  have h:=Bernstein.negative P (weightBoxes X B) I D hc
    (weightValues_mem (coefficientVector q) lam X B hX hlam) hx
  have he : weightedFunction (weightValues (coefficientVector q) lam) P=
      weightedFunction (weightValues (coefficientVector q) lam) (sourceFamily n 2) := by
    funext c
    unfold weightedFunction
    apply Finset.sum_congr rfl
    intro i _
    rw [familyIdentity_sound n 2 P hid i]
  rw [sourceFamily_second]
  change weightedFunction _ P x<0 at h
  rwa [he] at h

theorem center_mem_of_cell {d:ℕ} (C:Fin d→IntervalRat) (c:Fin d→ℝ)
    (hC:∀i,c i∈C i) (I:IntervalRat) (i:Fin d)
    (hb:I.lo≤(C i).lo ∧ (C i).hi≤I.hi) : c i∈I := by
  rw [IntervalRat.mem_def] at *
  have hl : (I.lo:ℝ)≤(C i).lo := by exact_mod_cast hb.1
  have hu : ((C i).hi:ℝ)≤I.hi := by exact_mod_cast hb.2
  exact ⟨hl.trans (hC i).1,(hC i).2.trans hu⟩

theorem cell_strict {r d:ℕ} (q:Tuning) (n:Fin r→ℤ) (lam:Fin r→ℝ)
    (X:Fin 3→IntervalRat) (B:Fin r→IntervalRat) (C:Fin d→IntervalRat) (c:Fin d→ℝ)
    (P0 P2:Fin (r*4)→QPoly) (D:ℕ) (cell:CoverCell d)
    (hid0:familyIdentityCheck n 0 P0=true) (hid2:familyIdentityCheck n 2 P2=true)
    (hc:cellCheck X B C P0 P2 D cell=true)
    (hX:∀i,coefficientVector q i∈X i) (hlam:∀j,lam j∈B j) (hC:∀i,c i∈C i)
    (hzero:∀i,indexedSymbol q n lam (c i)=0)
    (hslope:∀i,deriv (indexedSymbol q n lam) (c i)=0)
    {x:ℝ} (hx:x∈cell.1) (hne:∀i,x≠c i) : indexedSymbol q n lam x<0 := by
  cases he:cell.2 with
  | none=>
    have hcheck:Bernstein.check P0 (weightBoxes X B) cell.1 D=true:=by simpa only [cellCheck,he] using hc
    exact family0_negative q n lam X B P0 hid0 cell.1 D hcheck hX hlam hx
  | some i=>
    have hcheck : Bernstein.check P2 (weightBoxes X B) cell.1 D=true ∧
        cell.1.lo≤(C i).lo ∧ (C i).hi≤cell.1.hi := by
      simpa only [cellCheck,he,Bool.and_eq_true,decide_eq_true_eq] using hc
    have hci:=center_mem_of_cell C c hC cell.1 i hcheck.2
    obtain ⟨y,hy,hform⟩:=ModeLocking.Analysis.quadratic_taylor
      (fun z _=>(indexedSymbol_analytic q n lam z).contDiffAt) hci hx
      (hne i).symm (hzero i) (hslope i)
    rw [hform]
    have hyI:=uIcc_subset_Icc hci hx (Ioo_subset_Icc_self hy)
    have h2:=family2_negative q n lam X B P2 hid2 cell.1 D hcheck.1 hX hlam hyI
    have hn : x-c i≠0:=sub_ne_zero.mpr (hne i)
    rw [iteratedDeriv_eq_iterate]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h2 (sq_pos_of_ne_zero hn)) (by norm_num)

theorem cover_strict {r d:ℕ} (q:Tuning) (n:Fin r→ℤ) (lam:Fin r→ℝ)
    (X:Fin 3→IntervalRat) (B:Fin r→IntervalRat) (C:Fin d→IntervalRat) (c:Fin d→ℝ)
    (P0 P2:Fin (r*4)→QPoly) (D:ℕ) (cells:List (CoverCell d))
    (hid0:familyIdentityCheck n 0 P0=true) (hid2:familyIdentityCheck n 2 P2=true)
    (hc:coverCheck X B C P0 P2 D cells=true)
    (hX:∀i,coefficientVector q i∈X i) (hlam:∀j,lam j∈B j) (hC:∀i,c i∈C i)
    (hzero:∀i,indexedSymbol q n lam (c i)=0)
    (hslope:∀i,deriv (indexedSymbol q n lam) (c i)=0)
    {x:ℝ} (hx:x∈Icc (-1:ℝ) 1) (hne:∀i,x≠c i) : indexedSymbol q n lam x<0 := by
  simp only [coverCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨I,hI,hxI⟩:=Farey.Examples.intervalCoverCheck_covers hc.1.1 (by simpa only [Rat.cast_neg,Rat.cast_one] using hx.1) hx.2
  obtain ⟨cell,hcell,he⟩:=List.mem_map.mp hI
  exact cell_strict q n lam X B C c P0 P2 D cell hid0 hid2 (hc.1.2 cell hcell)
    hX hlam hC hzero hslope (he ▸ hxI) hne

theorem cover_curvature {r d:ℕ} (q:Tuning) (n:Fin r→ℤ) (lam:Fin r→ℝ)
    (X:Fin 3→IntervalRat) (B:Fin r→IntervalRat) (C:Fin d→IntervalRat) (c:Fin d→ℝ)
    (P0 P2:Fin (r*4)→QPoly) (D:ℕ) (cells:List (CoverCell d))
    (hid2:familyIdentityCheck n 2 P2=true) (hc:coverCheck X B C P0 P2 D cells=true)
    (hX:∀i,coefficientVector q i∈X i) (hlam:∀j,lam j∈B j) (hC:∀i,c i∈C i) (i:Fin d) :
    deriv^[2] (indexedSymbol q n lam) (c i)<0 := by
  simp only [coverCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨cell,hcell,he⟩:=hc.2 i
  have hcheck : Bernstein.check P2 (weightBoxes X B) cell.1 D=true ∧
      cell.1.lo≤(C i).lo ∧ (C i).hi≤cell.1.hi := by
    simpa only [cellCheck,he,Bool.and_eq_true,decide_eq_true_eq] using hc.1.2 cell hcell
  exact family2_negative q n lam X B P2 hid2 cell.1 D hcheck.1 hX hlam
    (center_mem_of_cell C c hC cell.1 i hcheck.2)

end
end polyak.CertifiedExamples.Plateaus
