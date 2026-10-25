import polyak.FareyPlateau.Ray.ContactTrigonometry

/-! Finite moment identities forced by the source admissibility equation. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set
open scoped BigOperators Classical
variable {I : Type*} [Fintype I]

def firstMoment (n : I→ℤ) (w : I→ℝ) : ℝ := ∑i,w i*(n i:ℝ)
def oneMoment (k : ℕ) (b : ℤ) (n : I→ℤ) (w : I→ℝ) : ℝ :=
  ∑i∈oneClass k b n,w i*(n i:ℝ)

theorem inverse_residue_nonzero {j k : ℕ} {b : ℤ} (hb : (b*j)%k=1) : b%k≠0 := by
  intro he
  have hh := hb
  rw [Int.mul_emod,he,zero_mul,Int.zero_emod] at hh
  omega

theorem admissible_moment_balance {j k : ℕ} {b : ℤ} (hb : (b*j)%k=1)
    {bar : ℝ} {n : I→ℤ} {w : I→ℝ} (h : Symbols.Admissible k b bar n w) :
    2*oneMoment k b n w-firstMoment n w=bar*oneMass k b n w := by
  have hb0 := inverse_residue_nonzero hb
  let Z := Finset.univ.filter (fun i=>n i%k=0)
  have hsplit : firstMoment n w=oneMoment k b n w+(∑i∈Z,w i*(n i:ℝ)) := by
    unfold firstMoment oneMoment oneClass Z
    rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases h.positions i with ho|hz
    · have hz : n i%k≠0 := by rw [ho]; exact hb0
      rw [ite_eq_left ho,ite_eq_right hz]
      ring
    · have ho : n i%k≠b%k := by rw [hz]; exact Ne.symm hb0
      rw [ite_eq_right ho,ite_eq_left hz]
      ring
  have hleft : (∑i∈oneClass k b n,w i*((n i:ℝ)-bar))=
      oneMoment k b n w-bar*oneMass k b n w := by
    unfold oneMoment oneMass
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hbalance := h.slope
  change (∑i∈oneClass k b n,w i*((n i:ℝ)-bar))=(∑i∈Z,w i*(n i:ℝ)) at hbalance
  rw [hleft] at hbalance
  linarith

theorem denominator_derivative_contact {j k : ℕ} (hk : 0<k) (hjk : 2*j≤k)
    {b : ℤ} (hb : (b*j)%k=1) {bar : ℝ} {n : I→ℤ} {w : I→ℝ}
    (h : Symbols.Admissible k b bar n w) :
    HasDerivAt (Symbols.denominator n w)
      (oneMoment k b n w*Real.sin (2*Real.pi/k)) (Regions.rationalAngle j k) := by
  have hder := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=>
    (((hasDerivAt_const (Regions.rationalAngle j k) (1:ℝ)).sub
      (((hasDerivAt_id (Regions.rationalAngle j k)).const_mul (n i:ℝ)).cos)).const_mul (w i)))
  have hval : (∑i,w i*(0-(-Real.sin ((n i:ℝ)*Regions.rationalAngle j k)*(n i:ℝ))))=
      oneMoment k b n w*Real.sin (2*Real.pi/k) := by
    unfold oneMoment
    rw [Finset.sum_mul]
    symm
    calc
      _=∑i∈oneClass k b n,w i*(0-(-Real.sin ((n i:ℝ)*Regions.rationalAngle j k)*(n i:ℝ))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(admissible_trig hk hjk hb h i).2]
        simp only [ite_eq_left hi]
        ring
      _=_ := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        rw [(admissible_trig hk hjk hb h i).2]
        simp [hi]
  simp only [id_eq,mul_one] at hder
  rw [hval] at hder
  exact hder

def sineMoment (n : I→ℤ) (w : I→ℝ) (ω : ℝ) : ℝ :=
  ∑i,w i*Real.sin ((n i:ℝ)*ω)

theorem sineMoment_derivative_contact {j k : ℕ} (hk : 0<k) (hjk : 2*j≤k)
    {b : ℤ} (hb : (b*j)%k=1) {bar : ℝ} {n : I→ℤ} {w : I→ℝ}
    (h : Symbols.Admissible k b bar n w) :
    HasDerivAt (sineMoment n w)
      (firstMoment n w+(Real.cos (2*Real.pi/k)-1)*oneMoment k b n w)
      (Regions.rationalAngle j k) := by
  have hder := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=>
    ((((hasDerivAt_id (Regions.rationalAngle j k)).const_mul (n i:ℝ)).sin).const_mul (w i)))
  have hval : (∑i,w i*(Real.cos ((n i:ℝ)*Regions.rationalAngle j k)*(n i:ℝ)))=
      firstMoment n w+(Real.cos (2*Real.pi/k)-1)*oneMoment k b n w := by
    unfold firstMoment oneMoment oneClass
    rw [Finset.mul_sum,Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [(admissible_trig hk hjk hb h i).1]
    by_cases hi : i∈oneClass k b n
    · have he : n i%k=b%k := (Finset.mem_filter.mp hi).2
      simp only [ite_eq_left hi,ite_eq_left he]
      ring
    · have he : n i%k≠b%k := by simpa [oneClass] using hi
      simp [hi,he]
  simp only [id_eq,mul_one] at hder
  rw [hval] at hder
  exact hder

end polyak.FareyPlateau.Ray
