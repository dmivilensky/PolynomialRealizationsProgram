import polyak.FareyPlateau.Symbols.Admissible
import polyak.FareyPlateau.Edge.Basic

/-! Actual residue arithmetic and the phase-floor contact value for every
admissible symbol.  Frequencies are the literal reduced Farey frequencies. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set
open scoped BigOperators Classical
variable {I : Type*} [Fintype I]

def oneClass (k : ℕ) (b : ℤ) (n : I→ℤ) : Finset I :=
  Finset.univ.filter (fun i=>n i%k=b%k)

def oneMass (k : ℕ) (b : ℤ) (n : I→ℤ) (w : I→ℝ) : ℝ :=
  ∑i∈oneClass k b n,w i

theorem oneMass_pos {k : ℕ} {b : ℤ} {bar : ℝ} {n : I→ℤ} {w : I→ℝ}
    (h : Symbols.Admissible k b bar n w) : 0<oneMass k b n w := by
  obtain ⟨i,_,_,hi,_⟩ := h.two_one
  apply Finset.sum_pos'
  · intro j _; exact (h.positive j).le
  · exact ⟨i,by simp [oneClass,hi],h.positive i⟩

theorem residue_product_one {j k : ℕ} {b n : ℤ} (hb : (b*j)%k=1)
    (hn : n%k=b%k) : (n*j)%k=1 := by
  rw [Int.mul_emod,hn,←Int.mul_emod,hb]

theorem residue_product_zero {j k : ℕ} {n : ℤ} (hn : n%k=0) : (n*j)%k=0 := by
  rw [Int.mul_emod,hn,zero_mul,Int.zero_emod]

theorem lag_trig_one {j k : ℕ} (hk : 0<k) (hjk : 2*j≤k) {b n : ℤ}
    (hb : (b*j)%k=1) (hn : n%k=b%k) :
    Real.cos ((n:ℝ)*Regions.rationalAngle j k)=Real.cos (2*Real.pi/k) ∧
      Real.sin ((n:ℝ)*Regions.rationalAngle j k)=Real.sin (2*Real.pi/k) := by
  have hh := Edge.lag_trig_reduce hk hjk n 0
  have ha : (Edge.atom j k hk hjk : ℝ)=Regions.rationalAngle j k := by
    dsimp [Edge.atom,Farey.gridFrequency,Regions.rationalAngle]
    push_cast
    ring
  rw [ha,residue_product_one hb hn] at hh
  simpa only [sub_zero,Int.cast_one,mul_one] using hh

theorem lag_trig_zero {j k : ℕ} (hk : 0<k) (hjk : 2*j≤k) {n : ℤ}
    (hn : n%k=0) :
    Real.cos ((n:ℝ)*Regions.rationalAngle j k)=1 ∧
      Real.sin ((n:ℝ)*Regions.rationalAngle j k)=0 := by
  have hh := Edge.lag_trig_reduce hk hjk n 0
  have ha : (Edge.atom j k hk hjk : ℝ)=Regions.rationalAngle j k := by
    dsimp [Edge.atom,Farey.gridFrequency,Regions.rationalAngle]
    push_cast
    ring
  rw [ha,residue_product_zero (j:=j) hn] at hh
  simpa only [sub_zero,Int.cast_zero,mul_zero,zero_div,Real.cos_zero,Real.sin_zero] using hh

theorem admissible_trig {j k : ℕ} (hk : 0<k) (hjk : 2*j≤k)
    {b : ℤ} (hb : (b*j)%k=1) {bar : ℝ} {n : I→ℤ} {w : I→ℝ}
    (h : Symbols.Admissible k b bar n w) (i : I) :
    Real.cos ((n i:ℝ)*Regions.rationalAngle j k)=
      (if i∈oneClass k b n then Real.cos (2*Real.pi/k) else 1) ∧
    Real.sin ((n i:ℝ)*Regions.rationalAngle j k)=
      (if i∈oneClass k b n then Real.sin (2*Real.pi/k) else 0) := by
  by_cases hi : i∈oneClass k b n
  · have hn : n i%k=b%k := (Finset.mem_filter.mp hi).2
    simpa [hi] using lag_trig_one hk hjk hb hn
  · have hn : n i%k≠b%k := by simpa [oneClass] using hi
    have hz := (h.positions i).resolve_left hn
    simpa [hi] using lag_trig_zero hk hjk hz

theorem denominator_contact {j k : ℕ} (hk : 0<k) (hjk : 2*j≤k)
    {b : ℤ} (hb : (b*j)%k=1) {bar : ℝ} {n : I→ℤ} {w : I→ℝ}
    (h : Symbols.Admissible k b bar n w) :
    Symbols.denominator n w (Regions.rationalAngle j k)=
      oneMass k b n w*(1-Real.cos (2*Real.pi/k)) := by
  unfold Symbols.denominator oneMass
  rw [Finset.sum_mul]
  symm
  calc
    _=∑i∈oneClass k b n,w i*(1-Real.cos ((n i:ℝ)*Regions.rationalAngle j k)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(admissible_trig hk hjk hb h i).1]
      simp [hi]
    _=_ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      rw [(admissible_trig hk hjk hb h i).1]
      simp [hi]

theorem sine_contact {j k : ℕ} (hk : 0<k) (hjk : 2*j≤k)
    {b : ℤ} (hb : (b*j)%k=1) {bar : ℝ} {n : I→ℤ} {w : I→ℝ}
    (h : Symbols.Admissible k b bar n w) :
    (∑i,w i*Real.sin ((n i:ℝ)*Regions.rationalAngle j k))=
      oneMass k b n w*Real.sin (2*Real.pi/k) := by
  unfold oneMass
  rw [Finset.sum_mul]
  symm
  calc
    _=∑i∈oneClass k b n,w i*Real.sin ((n i:ℝ)*Regions.rationalAngle j k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(admissible_trig hk hjk hb h i).2]
      simp [hi]
    _=_ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      rw [(admissible_trig hk hjk hb h i).2]
      simp [hi]

theorem phaseFloor_contact {j k : ℕ} (hj : 1≤j) (hjk : 2*j<k)
    {b : ℤ} (hb : (b*j)%k=1) {bar : ℝ} {n : I→ℤ} {w : I→ℝ}
    (h : Symbols.Admissible k b bar n w) :
    Symbols.psi n w (Chart.rationalCosine j k)=Chart.rationalHeight j k := by
  have hω := Regions.rationalAngle_mem hj hjk
  have hk : 0<k := by omega
  have hkr : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hγ : Real.pi/k∈Ioo (0:ℝ) Real.pi :=
    ⟨div_pos Real.pi_pos (by linarith),div_lt_self Real.pi_pos hkr⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi hγ.1 hγ.2
  have hμ := oneMass_pos h
  unfold Chart.rationalCosine Chart.rationalHeight
  rw [Symbols.psi_cos n w h.nonzero (fun i=>(h.positive i).le) h.normalization h.bezout hω,
    denominator_contact hk hjk.le hb h,sine_contact hk hjk.le hb h]
  rw [show 2*Real.pi/(k:ℝ)=2*(Real.pi/k) by ring,Real.sin_two_mul,Real.cos_two_mul]
  have hsq := Real.sin_sq_add_cos_sq (Real.pi/k)
  have hd : 1-(2*Real.cos (Real.pi/k)^2-1)=2*Real.sin (Real.pi/k)^2 := by nlinarith [hsq]
  rw [hd]
  field_simp [hs.ne',hμ.ne']

end polyak.FareyPlateau.Ray
