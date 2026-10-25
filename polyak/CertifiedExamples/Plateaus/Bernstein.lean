import polyak.Numerics.Polynomial
import polyak.Numerics.KernelDecide

/-! Bernstein bounds for a linear combination of rational polynomial sources.
All summands retain their common Bernstein index, so cancellations are checked
before a uniform coefficient bound is taken. Real coefficients may have either
sign and are enclosed by independently justified rational intervals. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus.Bernstein
open LeanCert.Core LeanCert.Engine Polynomial
open scoped BigOperators

def basis (D k:ℕ) (t:ℝ) : ℝ := (Nat.choose D k:ℝ)*t^k*(1-t)^(D-k)

theorem exists_parameter (I:IntervalRat) {x:ℝ} (hx:x∈I) :
    ∃t:ℝ,0≤t ∧ t≤1 ∧ x=(I.lo:ℝ)+((I.hi:ℝ)-I.lo)*t := by
  rw [IntervalRat.mem_def] at hx
  by_cases h:I.lo=I.hi
  · refine ⟨0,le_rfl,zero_le_one,?_⟩
    have he : (I.lo:ℝ)=(I.hi:ℝ) := by exact_mod_cast h
    nlinarith
  · have hp : (I.lo:ℝ)<I.hi := by exact_mod_cast lt_of_le_of_ne I.le h
    refine ⟨(x-I.lo)/((I.hi:ℝ)-I.lo),div_nonneg (by linarith) (by linarith),?_,?_⟩
    · rw [div_le_one (by linarith)]
      linarith
    · field_simp [show ((I.hi:ℝ)-I.lo)≠0 by linarith]
      ring

theorem representation (p:QPoly) (I:IntervalRat) (D:ℕ)
    (hlen:(QPoly.shiftedCoeffs p I).length=D+1) {t:ℝ} (ht:0≤t ∧ t≤1) :
    Polynomial.aeval ((I.lo:ℝ)+((I.hi:ℝ)-I.lo)*t) p.toPoly=
      ∑k∈Finset.range (D+1),
        ((QPoly.bernsteinCoeffs p I).getD k 0:ℝ)*basis D k t := by
  rw [QPoly.aeval_shiftedCoeffs,hlen]
  exact bernstein_representation (QPoly.shiftedCoeffs p I) D hlen t ht.1 ht.2

-- The recursive finite sum keeps the checker independent of any real decision procedure.
def sumBoxes : List IntervalRat→IntervalRat
  | []=>IntervalRat.singleton 0
  | A::As=>IntervalRat.add A (sumBoxes As)

theorem sumBoxes_ofFn_mem {m:ℕ} (A:Fin m→IntervalRat) {v:Fin m→ℝ}
    (h:∀j,v j∈A j) : (∑j,v j)∈sumBoxes (List.ofFn A) := by
  induction m with
  | zero=>simpa [sumBoxes] using IntervalRat.mem_singleton (0:ℚ)
  | succ m ih=>
    rw [List.ofFn_succ,Fin.sum_univ_succ]
    exact IntervalRat.mem_add (h 0) (ih (fun j=>A j.succ) (fun j=>h j.succ))

def controlBox {m:ℕ} (P:Fin m→QPoly) (W:Fin m→IntervalRat)
    (I:IntervalRat) (k:ℕ) : IntervalRat :=
  sumBoxes (List.ofFn fun j=>IntervalRat.mul (W j)
    (IntervalRat.singleton ((QPoly.bernsteinCoeffs (P j) I).getD k 0)))

theorem controlBox_mem {m:ℕ} (P:Fin m→QPoly) (W:Fin m→IntervalRat)
    (I:IntervalRat) (k:ℕ) {w:Fin m→ℝ} (hw:∀j,w j∈W j) :
    (∑j,w j*((QPoly.bernsteinCoeffs (P j) I).getD k 0:ℝ))∈controlBox P W I k := by
  exact sumBoxes_ofFn_mem _ (fun j=>IntervalRat.mem_mul (hw j) (IntervalRat.mem_singleton _))

def check {m:ℕ} (P:Fin m→QPoly) (W:Fin m→IntervalRat)
    (I:IntervalRat) (D:ℕ) : Bool :=
  decide (∀j,(QPoly.shiftedCoeffs (P j) I).length=D+1) &&
    decide (∀k:Fin (D+1),(controlBox P W I k.val).hi<0)

theorem negative {m:ℕ} (P:Fin m→QPoly) (W:Fin m→IntervalRat)
    (I:IntervalRat) (D:ℕ) (hc:check P W I D=true)
    {w:Fin m→ℝ} (hw:∀j,w j∈W j) {x:ℝ} (hx:x∈I) :
    (∑j,w j*Polynomial.aeval x (P j).toPoly)<0 := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hlen := hc.1
  have hhi := hc.2
  obtain ⟨t,ht0,ht1,rfl⟩:=exists_parameter I hx
  simp_rw [representation _ I D (hlen _) ⟨ht0,ht1⟩,Finset.mul_sum]
  rw [Finset.sum_comm]
  have he : (∑k∈Finset.range (D+1),∑j,
      w j*(((QPoly.bernsteinCoeffs (P j) I).getD k 0:ℝ)*basis D k t))=
      ∑k∈Finset.range (D+1),
        (∑j,w j*((QPoly.bernsteinCoeffs (P j) I).getD k 0:ℝ))*basis D k t := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  have hcoeff : ∀k∈Finset.range (D+1),
      (∑j,w j*((QPoly.bernsteinCoeffs (P j) I).getD k 0:ℝ))<0 := by
    intro k hk
    exact (controlBox_mem P W I k hw).2.trans_lt (by exact_mod_cast hhi ⟨k,Finset.mem_range.mp hk⟩)
  have hsum : (∑k∈Finset.range (D+1),basis D k t)=1 := bernstein_partition_of_unity D t
  obtain ⟨k,hk,hpos⟩ : ∃k∈Finset.range (D+1),0<basis D k t := by
    by_contra hn
    push Not at hn
    have hz : (∑k∈Finset.range (D+1),basis D k t)≤0 := Finset.sum_nonpos hn
    linarith
  apply neg_pos.mp
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_pos'
  · intro k hk
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (hcoeff k hk).le (bernstein_nonneg D k t ht0 ht1))
  · exact ⟨k,hk,neg_pos.mpr (mul_neg_of_neg_of_pos (hcoeff k hk) hpos)⟩

end polyak.CertifiedExamples.Plateaus.Bernstein
