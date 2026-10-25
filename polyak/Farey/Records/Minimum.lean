import polyak.Farey.Records.Basic

/-! The Farey basis determines the unique least nonnegative lattice
height over the complete integer strip, not a sampled subset of it. -/
namespace polyak.Farey

theorem recordLow_coprime {k j τ i m : ℤ} (hj : 2≤j) (hi : 0 < i) (hik : i < k)
    (he : j*τ=m*k+i) (hrec : RecordLow k j τ i) : Int.gcd m j=1 := by
  have hg := Int.gcd_pos_of_ne_zero_right m (by omega : j≠0)
  by_contra hn
  have hg1 : 1 < (Int.gcd m j:ℤ) := by exact_mod_cast (by omega : 1 < Int.gcd m j)
  obtain ⟨m',j',_,hm,hj'⟩ := Int.exists_gcd_one hg
  let y := j'*τ-m'*k
  have hiy : i=y*(Int.gcd m j:ℤ) := by
    dsimp [y]
    linear_combination -he+τ*hj'-k*hm
  have hjp : 0 < j' := by nlinarith [hj']
  have hjj : j' < j := by nlinarith [hj']
  have hyp : 0 < y := by nlinarith [hiy]
  have hyi : y < i := by nlinarith [hiy]
  have hr : residue k τ j'=y :=
    residue_eq_of_lattice hyp.le (hyi.trans hik) (q:=m') (by dsimp [y];ring)
  have hh := hrec j' (by omega) hjj
  rw [hr] at hh
  omega

def RightParent.upperHeight {m j : ℤ} (R : RightParent m j) (k τ : ℤ) : ℤ :=
  R.leftDen*τ-R.leftNum*k

def RightParent.lowerHeight {m j : ℤ} (R : RightParent m j) (k τ : ℤ) : ℤ :=
  R.den*τ-R.num*k

theorem RightParent.height_determinant {m j : ℤ} (R : RightParent m j) (k τ : ℤ) :
    R.leftDen*R.lowerHeight k τ-R.den*R.upperHeight k τ= -k := by
  dsimp [upperHeight,lowerHeight,leftDen,leftNum]
  linear_combination -k*R.determinant

theorem RightParent.lattice_height_basis {m j : ℤ} (R : RightParent m j)
    (k τ p y q : ℤ) (he : p*τ=q*k+y) :
    ∃a b : ℤ,p=a*R.leftDen+b*R.den ∧
      y=a*R.upperHeight k τ+b*R.lowerHeight k τ := by
  let a := R.num*p-R.den*q
  let b := R.leftDen*q-R.leftNum*p
  obtain ⟨hp,hq⟩ := R.lattice_basis p q
  change a*R.leftDen+b*R.den=p at hp
  change a*R.leftNum+b*R.num=q at hq
  refine ⟨a,b,hp.symm,?_⟩
  dsimp [upperHeight,lowerHeight]
  linear_combination -he-τ*hp+k*hq

theorem RightParent.heights {k j τ i m : ℤ} (R : RightParent m j)
    (he : j*τ=m*k+i) :
    j*R.upperHeight k τ=k+R.leftDen*i ∧
    j*R.lowerHeight k τ=R.den*i-k ∧
    R.upperHeight k τ+R.lowerHeight k τ=i := by
  dsimp [upperHeight,lowerHeight]
  refine ⟨?_,?_,?_⟩
  · linear_combination R.leftDen*he+k*R.left_determinant
  · linear_combination R.den*he-k*R.determinant
  · dsimp [leftDen,leftNum]
    linear_combination he

theorem RightParent.residue_at_left {k j τ i m : ℤ} (R : RightParent m j)
    (hi : 0 < i) (hik : i < k) (he : j*τ=m*k+i) (hcut : i*R.den < k) :
    residue k τ R.leftDen=R.upperHeight k τ ∧
    i < R.upperHeight k τ ∧ R.upperHeight k τ < k ∧ R.lowerHeight k τ < 0 := by
  have hj : 0 < j := R.den_pos.trans R.den_lt
  obtain ⟨hu,hv,_⟩ := R.heights he
  have hiu : i < R.upperHeight k τ := by dsimp [leftDen] at hu; nlinarith
  have huk : R.upperHeight k τ < k := by
    have hl := R.leftDen_pos
    have hid : j*k-(k+R.leftDen*i)=(R.den-1)*k+R.leftDen*(k-i) := by
      dsimp [leftDen]
      ring
    have hd := R.den_pos
    have hnon : 0≤(R.den-1)*k := mul_nonneg (by omega) (by omega)
    have hpos : 0 < R.leftDen*(k-i) := mul_pos hl (by omega)
    nlinarith
  have hvn : R.lowerHeight k τ < 0 := by nlinarith
  exact ⟨residue_eq_of_lattice (by omega) huk (q:=R.leftNum)
    (by dsimp [upperHeight];ring),hiu,huk,hvn⟩

theorem RightParent.strip_minimum {k j τ i m : ℤ} (R : RightParent m j)
    (hi : 0 < i) (hik : i < k) (he : j*τ=m*k+i) (hcut : i*R.den < k)
    (p : ℤ) (hp : 1≤p) (hpj : p < j) :
    R.upperHeight k τ≤residue k τ p ∧
      (residue k τ p=R.upperHeight k τ ↔ p=R.leftDen) := by
  obtain ⟨hr,hiu,_,hvn⟩ := R.residue_at_left hi hik he hcut
  let y := residue k τ p
  let q := p*τ/k
  let a := R.num*p-R.den*q
  let b := R.leftDen*q-R.leftNum*p
  have hy : 0≤y := Int.emod_nonneg _ (by omega)
  have hpy : p*τ=q*k+y := (Int.ediv_mul_add_emod (p*τ) k).symm
  obtain ⟨hpab,hqab⟩ := R.lattice_basis p q
  change a*R.leftDen+b*R.den=p at hpab
  change a*R.leftNum+b*R.num=q at hqab
  have hyab : y=a*R.upperHeight k τ+b*R.lowerHeight k τ := by
    dsimp [upperHeight,lowerHeight]
    linear_combination -hpy-τ*hpab+k*hqab
  have hapos : 1≤a := by
    by_contra hn
    have ha : a≤0 := by omega
    have hb : 1≤b := by
      by_contra hn
      have hb : b≤0 := by omega
      have h1 := mul_nonpos_of_nonpos_of_nonneg ha R.leftDen_pos.le
      have h2 := mul_nonpos_of_nonpos_of_nonneg hb R.den_pos.le
      linarith
    have h1 := mul_nonpos_of_nonpos_of_nonneg ha (by omega : 0≤R.upperHeight k τ)
    have h2 : b*R.lowerHeight k τ < 0 := mul_neg_of_pos_of_neg (by omega) hvn
    linarith
  have hbnon : b≤0 := by
    by_contra hn
    have hb : 1≤b := by omega
    have h1 := mul_le_mul_of_nonneg_right hapos R.leftDen_pos.le
    have h2 := mul_le_mul_of_nonneg_right hb R.den_pos.le
    have hl : R.leftDen+R.den=j := by dsimp [leftDen];ring
    linarith
  have h1 := mul_le_mul_of_nonneg_right hapos (by omega : 0≤R.upperHeight k τ)
  have h2 := mul_nonneg_of_nonpos_of_nonpos hbnon hvn.le
  have hmin : R.upperHeight k τ≤y := by linarith
  refine ⟨hmin,?_⟩
  constructor
  · intro heq
    have ha1 : a=1 := by
      by_contra hn
      have ha2 : 2≤a := by omega
      have hh := mul_le_mul_of_nonneg_right ha2 (by omega : 0≤R.upperHeight k τ)
      change y=R.upperHeight k τ at heq
      nlinarith
    have hb0 : b=0 := by
      by_contra hn
      have hb1 : b≤ -1 := by omega
      have hh := mul_le_mul_of_nonpos_right hb1 hvn.le
      change y=R.upperHeight k τ at heq
      rw [ha1,one_mul] at hyab
      nlinarith
    rw [ha1,hb0,one_mul,zero_mul,add_zero] at hpab
    exact hpab.symm
  · intro heq
    rw [heq]
    exact hr

end polyak.Farey
