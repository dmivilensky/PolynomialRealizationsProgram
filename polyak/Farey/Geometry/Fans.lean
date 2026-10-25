import polyak.Farey.Positions.Permutation
import polyak.Farey.Records.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! Both complete Farey fans: actual parents, reduced lattice points,
neighbour identities, convergence, and all points on each lattice line. -/
noncomputable section
namespace polyak.Farey
open Filter
open scoped Topology

abbrev ParentData := Levels.Lattice.FareyParents

theorem exists_parents {j k : ℤ} (hk : 2≤k) (hjk : Int.gcd j k=1) :
    Nonempty (ParentData j k) := by
  obtain ⟨R⟩ := exists_rightParent hk hjk
  exact ⟨⟨j-R.num,k-R.den,R.num,R.den,by ring,by ring,
    by linear_combination R.determinant,by linarith [R.den_lt],R.den_pos⟩⟩

def lowerFan {j k : ℤ} (P : ParentData j k) (m : ℤ) : ℤ×ℤ :=
  (P.a+m*j,P.b+m*k)

def upperFan {j k : ℤ} (P : ParentData j k) (m : ℤ) : ℤ×ℤ :=
  (P.c+m*j,P.d+m*k)

theorem lowerFan_line {j k : ℤ} (P : ParentData j k) (m : ℤ) :
    k*(lowerFan P m).1-j*(lowerFan P m).2= -1 := by
  dsimp [lowerFan]
  linear_combination -P.lower_bezout

theorem upperFan_line {j k : ℤ} (P : ParentData j k) (m : ℤ) :
    k*(upperFan P m).1-j*(upperFan P m).2=1 := by
  dsimp [upperFan]
  linear_combination P.upper_bezout

theorem lowerFan_coprime {j k : ℤ} (P : ParentData j k) (m : ℤ) :
    IsCoprime (lowerFan P m).1 (lowerFan P m).2 := by
  exact ⟨-k,j,by linear_combination -lowerFan_line P m⟩

theorem upperFan_coprime {j k : ℤ} (P : ParentData j k) (m : ℤ) :
    IsCoprime (upperFan P m).1 (upperFan P m).2 := by
  exact ⟨k,-j,by linear_combination upperFan_line P m⟩

theorem lowerFan_neighbors {j k : ℤ} (P : ParentData j k) (m : ℤ) :
    (lowerFan P m).2*(lowerFan P (m+1)).1-
      (lowerFan P m).1*(lowerFan P (m+1)).2=1 := by
  dsimp [lowerFan]
  linear_combination P.lower_bezout

theorem upperFan_neighbors {j k : ℤ} (P : ParentData j k) (m : ℤ) :
    (upperFan P m).1*(upperFan P (m+1)).2-
      (upperFan P m).2*(upperFan P (m+1)).1=1 := by
  dsimp [upperFan]
  linear_combination P.upper_bezout

theorem lowerFan_den_pos {j k : ℤ} (P : ParentData j k) {m : ℤ} (hm : 0≤m) :
    0<(lowerFan P m).2 := by
  dsimp [lowerFan]
  exact add_pos_of_pos_of_nonneg P.b_pos (mul_nonneg hm P.period_pos.le)

theorem upperFan_den_pos {j k : ℤ} (P : ParentData j k) {m : ℤ} (hm : 0≤m) :
    0<(upperFan P m).2 := by
  dsimp [upperFan]
  exact add_pos_of_pos_of_nonneg P.d_pos (mul_nonneg hm P.period_pos.le)

theorem lowerFan_below {j k : ℤ} (P : ParentData j k) {m : ℤ} (hm : 0≤m) :
    ((lowerFan P m).1:ℝ)/(lowerFan P m).2<(j:ℝ)/k := by
  have hd : (0:ℝ)<(lowerFan P m).2 := by exact_mod_cast lowerFan_den_pos P hm
  have hk : (0:ℝ)<k := by exact_mod_cast P.period_pos
  rw [div_lt_div_iff₀ hd hk]
  have he : (k:ℝ)*(lowerFan P m).1-j*(lowerFan P m).2= -1 := by exact_mod_cast lowerFan_line P m
  linarith

theorem upperFan_above {j k : ℤ} (P : ParentData j k) {m : ℤ} (hm : 0≤m) :
    (j:ℝ)/k<((upperFan P m).1:ℝ)/(upperFan P m).2 := by
  have hd : (0:ℝ)<(upperFan P m).2 := by exact_mod_cast upperFan_den_pos P hm
  have hk : (0:ℝ)<k := by exact_mod_cast P.period_pos
  rw [div_lt_div_iff₀ hk hd]
  have he : (k:ℝ)*(upperFan P m).1-j*(upperFan P m).2=1 := by exact_mod_cast upperFan_line P m
  linarith

theorem lowerFan_tendsto {j k : ℤ} (P : ParentData j k) :
    Tendsto (fun m : ℕ=>((lowerFan P m).1:ℝ)/(lowerFan P m).2) atTop (𝓝 ((j:ℝ)/k)) := by
  have hk : (k:ℝ)≠0 := by exact_mod_cast (ne_of_gt P.period_pos)
  simpa only [lowerFan,Int.cast_add,Int.cast_mul,Int.cast_natCast,mul_comm (j:ℝ),mul_comm (k:ℝ)] using
    tendsto_add_mul_div_add_mul_atTop_nhds (P.a:ℝ) (P.b:ℝ) (j:ℝ) hk

theorem upperFan_tendsto {j k : ℤ} (P : ParentData j k) :
    Tendsto (fun m : ℕ=>((upperFan P m).1:ℝ)/(upperFan P m).2) atTop (𝓝 ((j:ℝ)/k)) := by
  have hk : (k:ℝ)≠0 := by exact_mod_cast (ne_of_gt P.period_pos)
  simpa only [upperFan,Int.cast_add,Int.cast_mul,Int.cast_natCast,mul_comm (j:ℝ),mul_comm (k:ℝ)] using
    tendsto_add_mul_div_add_mul_atTop_nhds (P.c:ℝ) (P.d:ℝ) (j:ℝ) hk

theorem lowerFan_line_complete {j k : ℤ} (P : ParentData j k) (x y : ℤ) :
    (k*x-j*y= -1 ∧ P.b<y) ↔ ∃m : ℤ,1≤m ∧ (x,y)=lowerFan P m := by
  constructor
  · rintro ⟨he,hy⟩
    let m:=P.b*x-P.a*y
    have hx : x=P.a+m*j := by dsimp [m]; linear_combination -x*P.lower_bezout-P.a*he
    have hy' : y=P.b+m*k := by dsimp [m]; linear_combination -y*P.lower_bezout-P.b*he
    have hm : 0<m := by nlinarith [P.period_pos]
    exact ⟨m,by omega,by simp only [lowerFan,hx,hy']⟩
  · rintro ⟨m,hm,he⟩
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp [lowerFan] at hx hy
    constructor
    · rw [hx,hy]
      exact lowerFan_line P m
    · nlinarith [P.period_pos]

theorem upperFan_line_complete {j k : ℤ} (P : ParentData j k) (x y : ℤ) :
    (k*x-j*y=1 ∧ P.d<y) ↔ ∃m : ℤ,1≤m ∧ (x,y)=upperFan P m := by
  constructor
  · rintro ⟨he,hy⟩
    let m:=P.c*y-P.d*x
    have hx : x=P.c+m*j := by dsimp [m]; linear_combination -x*P.upper_bezout+P.c*he
    have hy' : y=P.d+m*k := by dsimp [m]; linear_combination -y*P.upper_bezout+P.d*he
    have hm : 0<m := by nlinarith [P.period_pos]
    exact ⟨m,by omega,by simp only [upperFan,hx,hy']⟩
  · rintro ⟨m,hm,he⟩
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp [upperFan] at hx hy
    constructor
    · rw [hx,hy]
      exact upperFan_line P m
    · nlinarith [P.period_pos]

end polyak.Farey
