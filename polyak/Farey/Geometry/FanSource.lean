import polyak.Farey.Geometry.LevelTwo

/-! Literal special-fan and line-height consequences used in the source. -/
noncomputable section
namespace polyak.Farey
open Filter Levels
open scoped Topology

theorem lowerFan_all_line_iff {j k : ℤ} (P : ParentData j k) (x y : ℤ) :
    k*x-j*y= -1 ↔ ∃m : ℤ,(x,y)=lowerFan P m := by
  constructor
  · intro he
    let m:=P.b*x-P.a*y
    have hx : x=P.a+m*j := by dsimp [m]; linear_combination -x*P.lower_bezout-P.a*he
    have hy : y=P.b+m*k := by dsimp [m]; linear_combination -y*P.lower_bezout-P.b*he
    exact ⟨m,by simp only [lowerFan,hx,hy]⟩
  · rintro ⟨m,he⟩
    have hx:=congrArg Prod.fst he
    have hy:=congrArg Prod.snd he
    change x=(lowerFan P m).1 at hx
    change y=(lowerFan P m).2 at hy
    rw [hx,hy]
    exact lowerFan_line P m

theorem upperFan_all_line_iff {j k : ℤ} (P : ParentData j k) (x y : ℤ) :
    k*x-j*y=1 ↔ ∃m : ℤ,(x,y)=upperFan P m := by
  constructor
  · intro he
    let m:=P.c*y-P.d*x
    have hx : x=P.c+m*j := by dsimp [m]; linear_combination -x*P.upper_bezout+P.c*he
    have hy : y=P.d+m*k := by dsimp [m]; linear_combination -y*P.upper_bezout+P.d*he
    exact ⟨m,by simp only [upperFan,hx,hy]⟩
  · rintro ⟨m,he⟩
    have hx:=congrArg Prod.fst he
    have hy:=congrArg Prod.snd he
    change x=(upperFan P m).1 at hx
    change y=(upperFan P m).2 at hy
    rw [hx,hy]
    exact upperFan_line P m

def unitFractionParents (K : ℤ) (hK : 2≤K) : ParentData 1 K where
  a:=0
  b:=1
  c:=1
  d:=K-1
  numerator:=by norm_num
  denominator:=by ring
  determinant:=by ring
  b_pos:=by norm_num
  d_pos:=by omega

@[simp] theorem unitFraction_lowerFan (K : ℤ) (hK : 2≤K) (m : ℤ) :
    lowerFan (unitFractionParents K hK) m=(m,fanDenominator K m) := by
  apply Prod.ext
  · simp only [lowerFan,unitFractionParents,zero_add,mul_one]
  · dsimp [lowerFan,unitFractionParents,fanDenominator]
    ring

@[simp] theorem unitFraction_upperFan (K : ℤ) (hK : 2≤K) (m : ℤ) :
    upperFan (unitFractionParents (K+1) (by omega)) m=upperSpine K m := by
  apply Prod.ext
  · dsimp [upperFan,unitFractionParents,upperSpine]
    ring
  · dsimp [upperFan,unitFractionParents,upperSpine]
    ring

theorem lower_spine_tendsto {K : ℤ} (hK : 2≤K) :
    Tendsto (fun p : ℕ=>(p:ℝ)/fanDenominator K p) atTop (𝓝 (1/(K:ℝ))) := by
  have hk : (K:ℝ)≠0 := by exact_mod_cast (show K≠0 by omega)
  simpa only [fanDenominator,Int.cast_add,Int.cast_one,Int.cast_mul,Int.cast_natCast,
    zero_add,one_mul,mul_comm (K:ℝ),add_comm (1:ℝ)] using
    tendsto_add_mul_div_add_mul_atTop_nhds (0:ℝ) 1 1 hk

theorem upper_spine_tendsto {K : ℤ} (hK : 2≤K) :
    Tendsto (fun m : ℕ=>((upperSpine K m).1:ℝ)/(upperSpine K m).2)
      atTop (𝓝 (1/((K:ℝ)+1))) := by
  have hk : (K:ℝ)+1≠0 := by
    have hh : (2:ℝ)≤K := by exact_mod_cast hK
    linarith
  simpa only [upperSpine,Int.cast_add,Int.cast_one,Int.cast_mul,Int.cast_natCast,
    one_mul,mul_comm ((K:ℝ)+1),add_comm (1:ℝ)] using
    tendsto_add_mul_div_add_mul_atTop_nhds (1:ℝ) K 1 hk

theorem lower_spine_initial (K : ℤ) : fanDenominator K 1=K+1 := by simp [fanDenominator]

theorem lower_spine_parent_order {K p : ℤ} (hK : 2≤K) (hp : 2≤p) :
    ((p-1:ℤ):ℝ)/fanDenominator K (p-1)<(p:ℝ)/fanDenominator K p ∧
      (p:ℝ)/fanDenominator K p<1/(K:ℝ) := by
  constructor
  · simpa only [lowerFan,spineParents,zero_mul,add_zero] using
      lowerFan_below (spineParents K p hK hp) (m:=0) (by norm_num)
  · exact (lower_spine_in_window hK hp).2

theorem lower_spine_dirac_iff (Θ : Curve) {K p : ℕ} (hK : 2≤K) (hp : 1≤p)
    (ω : Frequency) (hω : (ω:ℝ)=2*Real.pi*p/(p*K+1)) :
    ProgramSolution Θ nonzeroLags (MeasureTheory.Measure.dirac ω) ↔
      Θ ω≤Real.pi-(K:ℝ)*(ω:ℝ)/2 := by
  have hh : IsCoprime (p:ℤ) ((p*K+1:ℕ):ℤ) := by
    simpa only [fanDenominator,Nat.cast_add,Nat.cast_one,Nat.cast_mul] using lower_spine_coprime K p
  have hcop : p.Coprime (p*K+1) := by
    simpa only [Int.gcd_natCast_natCast] using Int.isCoprime_iff_gcd_eq_one.mp hh
  have hk : 2≤p*K+1 := by nlinarith
  have hωnat : (ω:ℝ)=2*Real.pi*p/((p*K+1:ℕ):ℝ) := by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hω
  have hden : fanDenominator (K:ℤ) p≠0 := ne_of_gt
    (fanDenominator_pos (by exact_mod_cast hK) (by exact_mod_cast hp))
  have hphase : Real.pi-(K:ℝ)*(ω:ℝ)/2=Real.pi/((p*K+1:ℕ):ℝ) := by
    rw [hωnat]
    simpa only [fanDenominator,Int.cast_add,Int.cast_one,Int.cast_mul,Int.cast_natCast,
      Nat.cast_add,Nat.cast_one,Nat.cast_mul] using lower_spine_phase (K:ℤ) p hden
  rw [Lattice.rational_atom_program_iff Θ hcop hk ω hωnat,hphase]

theorem upper_spine_dirac_iff (Θ : Curve) {K m : ℕ} (hK : 2≤K) (hm : 1≤m)
    (ω : Frequency) (hω : (ω:ℝ)=2*Real.pi*(m+1)/(K+m*(K+1))) :
    ProgramSolution Θ nonzeroLags (MeasureTheory.Measure.dirac ω) ↔
      Θ ω≤((K:ℝ)+1)*(ω:ℝ)/2-Real.pi := by
  have hh : IsCoprime ((m+1:ℕ):ℤ) ((K+m*(K+1):ℕ):ℤ) := by
    simpa only [upperSpine,Nat.cast_add,Nat.cast_one,Nat.cast_mul] using upper_spine_coprime K m
  have hcop : (m+1).Coprime (K+m*(K+1)) := by
    simpa only [Int.gcd_natCast_natCast] using Int.isCoprime_iff_gcd_eq_one.mp hh
  have hk : 2≤K+m*(K+1) := by nlinarith
  have hωnat : (ω:ℝ)=2*Real.pi*((m+1:ℕ):ℝ)/((K+m*(K+1):ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hω
  have hden : (upperSpine (K:ℤ) m).2≠0 := by
    dsimp [upperSpine]
    have hk' : (2:ℤ)≤K := by exact_mod_cast hK
    have hm' : (1:ℤ)≤m := by exact_mod_cast hm
    nlinarith
  have hphase : ((K:ℝ)+1)*(ω:ℝ)/2-Real.pi=Real.pi/((K+m*(K+1):ℕ):ℝ) := by
    rw [hωnat]
    simpa only [upperSpine,Int.cast_add,Int.cast_one,Int.cast_mul,Int.cast_natCast,
      Nat.cast_add,Nat.cast_one,Nat.cast_mul] using upper_spine_phase (K:ℤ) m hden
  rw [Lattice.rational_atom_program_iff Θ hcop hk ω hωnat,hphase]

end polyak.Farey
