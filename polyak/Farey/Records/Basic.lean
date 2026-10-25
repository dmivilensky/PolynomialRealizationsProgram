import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-! Exact integer coordinates for a Farey record. Numerators may be
arbitrary integers; no reduction to fractions between zero and one is used. -/
namespace polyak.Farey

def residue (k τ p : ℤ) : ℤ := p*τ%k

structure RightParent (m j : ℤ) where
  num : ℤ
  den : ℤ
  determinant : num*j-m*den=1
  den_pos : 0 < den
  den_lt : den < j

theorem exists_rightParent {m j : ℤ} (hj : 2≤j) (h : Int.gcd m j=1) :
    Nonempty (RightParent m j) := by
  let x := Int.gcdA m j
  let y := Int.gcdB m j
  have he : m*x+j*y=1 := by
    simpa only [x,y,h,Nat.cast_one] using (Int.gcd_eq_gcd_ab m j).symm
  let d := (-x)%j
  let r := y-m*((-x)/j)
  have hd0 : 0≤d := Int.emod_nonneg _ (by omega)
  have hdj : d < j := Int.emod_lt_of_pos _ (by omega)
  have hdiv := Int.emod_add_ediv_mul (-x) j
  change d+((-x)/j)*j= -x at hdiv
  have hdet : r*j-m*d=1 := by dsimp [r]; linear_combination he-m*hdiv
  have hd : 0 < d := by
    by_contra hn
    have hz : d=0 := by omega
    rw [hz,mul_zero,sub_zero] at hdet
    by_cases hr : r≤0
    · nlinarith
    · have hr1 : 1≤r := by omega
      nlinarith
  exact ⟨⟨r,d,hdet,hd,hdj⟩⟩

def RightParent.leftDen {m j : ℤ} (R : RightParent m j) : ℤ := j-R.den
def RightParent.leftNum {m j : ℤ} (R : RightParent m j) : ℤ := m-R.num

theorem RightParent.left_determinant {m j : ℤ} (R : RightParent m j) :
    m*R.leftDen-R.leftNum*j=1 := by
  dsimp [leftDen,leftNum]
  nlinarith [R.determinant]

theorem RightParent.leftDen_pos {m j : ℤ} (R : RightParent m j) : 0 < R.leftDen := by
  dsimp [leftDen]
  linarith [R.den_lt]

theorem RightParent.leftDen_lt {m j : ℤ} (R : RightParent m j) : R.leftDen < j := by
  dsimp [leftDen]
  linarith [R.den_pos]

theorem RightParent.unique {m j : ℤ} (R S : RightParent m j) : R=S := by
  have hj : 0 < j := R.den_pos.trans R.den_lt
  have hid : R.den-S.den=j*(S.num*R.den-R.num*S.den) := by
    linear_combination S.den*R.determinant-R.den*S.determinant
  have ht0 : -1 < S.num*R.den-R.num*S.den := by
    by_contra hn
    have hmul : j*(S.num*R.den-R.num*S.den)≤ -j := by nlinarith
    linarith [R.den_pos,R.den_lt,S.den_pos,S.den_lt]
  have ht1 : S.num*R.den-R.num*S.den < 1 := by
    by_contra hn
    have hmul : j≤j*(S.num*R.den-R.num*S.den) := by nlinarith
    linarith [R.den_pos,R.den_lt,S.den_pos,S.den_lt]
  have he : R.den=S.den := by
    have ht : S.num*R.den-R.num*S.den=0 := by omega
    rw [ht,mul_zero] at hid
    omega
  have hn : R.num=S.num := by
    have hR := R.determinant
    rw [he] at hR
    apply mul_right_cancel₀ hj.ne'
    linarith [S.determinant]
  cases R
  cases S
  simp_all

def RecordLow (k j τ i : ℤ) : Prop := ∀p : ℤ,1≤p→p < j→i < residue k τ p

theorem residue_eq_of_lattice {k τ p y q : ℤ} (hy0 : 0≤y) (hyk : y < k)
    (he : p*τ=q*k+y) : residue k τ p=y := by
  unfold residue
  rw [he,add_comm,Int.add_mul_emod_self_right]
  exact Int.emod_eq_of_lt hy0 hyk

theorem RightParent.lattice_basis {m j : ℤ} (R : RightParent m j) (p q : ℤ) :
    (R.num*p-R.den*q)*R.leftDen+(R.leftDen*q-R.leftNum*p)*R.den=p ∧
    (R.num*p-R.den*q)*R.leftNum+(R.leftDen*q-R.leftNum*p)*R.num=q := by
  dsimp [leftDen,leftNum]
  constructor
  · linear_combination p*R.determinant
  · linear_combination q*R.determinant

end polyak.Farey
