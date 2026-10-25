import polyak.Farey.Certificates.Polynomial

/-! The full finite fan formula, with both lower and upper signed lags. -/
noncomputable section
namespace polyak.Farey.Certificates
open Levels Set
open Spectral (chebT chebU)
open scoped BigOperators

def fanLags (K:ℕ) : Set ℤ :=
  {n | ∃m:ℕ,n=(m*K+1:ℕ)} ∪ {n | ∃m:ℕ,0<m ∧ n= -((m*K:ℕ):ℤ)}

theorem fanLags_nonzero {K:ℕ} (hK:0<K) {n:ℤ} (hn:n∈fanLags K) : n≠0 := by
  rcases hn with ⟨m,rfl⟩|⟨m,hm,rfl⟩
  · omega
  · have hp:=Nat.mul_pos hm hK
    omega

def fanLeft (q:General.Tuning) (K:ℕ) (P N:Finset ℕ) (a b:ℕ→ℝ) (γ c:ℝ) : ℝ:=
  q.Xi c*((∑m∈P,a m*(1-chebT (m*K+1) c))+
    (∑m∈N,b m*(1-chebT (m*K) c))+γ)

def fanRight (K:ℕ) (P N:Finset ℕ) (a b:ℕ→ℝ) (c:ℝ) : ℝ:=
  (1-c^2)*((∑m∈P,a m*chebU (m*K) c)-(∑m∈N,b m*chebU (m*K-1) c))

def familyLag (K:ℕ) {P N:Finset ℕ} : Sum {m//m∈P} {m//m∈N}→ℤ
  | .inl m => (m.val*K+1:ℕ)
  | .inr m => -((m.val*K:ℕ):ℤ)

def familyWeight (a b:ℕ→ℝ) {P N:Finset ℕ} : Sum {m//m∈P} {m//m∈N}→ℝ
  | .inl m => a m
  | .inr m => b m

theorem signedLagPolynomial_pos (q:General.Tuning) {n:ℕ} (hn:0<n) (c:ℝ) :
    signedLagPolynomial q (n:ℤ) c=q.Xi c*(1-chebT n c)-(1-c^2)*chebU (n-1) c := by
  have hs : (n:ℤ).sign=1:=Int.sign_eq_one_of_pos (by exact_mod_cast hn)
  simp only [signedLagPolynomial,Int.natAbs_natCast,hs,Int.cast_one,one_mul]

theorem signedLagPolynomial_neg (q:General.Tuning) {n:ℕ} (hn:0<n) (c:ℝ) :
    signedLagPolynomial q (-(n:ℤ)) c=q.Xi c*(1-chebT n c)+(1-c^2)*chebU (n-1) c := by
  have hs : (n:ℤ).sign=1:=Int.sign_eq_one_of_pos (by exact_mod_cast hn)
  simp only [signedLagPolynomial,Int.natAbs_neg,Int.natAbs_natCast,Int.sign_neg,hs,
    Int.cast_neg,Int.cast_one,neg_one_mul]
  ring

theorem fan_polynomial_identity (q:General.Tuning) {K:ℕ} (hK:0<K) (P N:Finset ℕ)
    (hN:∀m∈N,0<m) (a b:ℕ→ℝ) (γ c:ℝ) :
    indexedPolynomial q (familyLag K (P:=P) (N:=N)) (familyWeight a b) γ c=
      fanLeft q K P N a b γ c-fanRight K P N a b c := by
  classical
  unfold indexedPolynomial
  rw [Fintype.sum_sum_type]
  simp only [familyLag,familyWeight]
  simp_rw [signedLagPolynomial_pos q (Nat.succ_pos _)]
  have hnegative (m:{m//m∈N}) : 0<m.val*K:=Nat.mul_pos (hN _ m.property) hK
  simp_rw [signedLagPolynomial_neg q (hnegative _)]
  change (∑m:{m//m∈P},a m.val*(q.Xi c*(1-chebT (m.val*K+1) c)-
      (1-c^2)*chebU (m.val*K) c))+
    (∑m:{m//m∈N},b m.val*(q.Xi c*(1-chebT (m.val*K) c)+
      (1-c^2)*chebU (m.val*K-1) c))+γ*q.Xi c=_
  rw [Finset.sum_coe_sort P (fun m:ℕ=>a m*(q.Xi c*(1-chebT (m*K+1) c)-
      (1-c^2)*chebU (m*K) c)),
    Finset.sum_coe_sort N (fun m:ℕ=>b m*(q.Xi c*(1-chebT (m*K) c)+
      (1-c^2)*chebU (m*K-1) c))]
  have hp (m:ℕ) : a m*(q.Xi c*(1-chebT (m*K+1) c)-(1-c^2)*chebU (m*K) c)=
      q.Xi c*(a m*(1-chebT (m*K+1) c))-(1-c^2)*(a m*chebU (m*K) c) := by ring
  have hn (m:ℕ) : b m*(q.Xi c*(1-chebT (m*K) c)+(1-c^2)*chebU (m*K-1) c)=
      q.Xi c*(b m*(1-chebT (m*K) c))+(1-c^2)*(b m*chebU (m*K-1) c) := by ring
  simp_rw [hp,hn,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum]
  unfold fanLeft fanRight
  ring

theorem fan_formula_rate_lt_one (q:General.Tuning) {K:ℕ} (hK:2≤K) (P N:Finset ℕ)
    (hN:∀m∈N,0<m) (a b:ℕ→ℝ) (ha:∀m∈P,0≤a m) (hb:∀m∈N,0≤b m)
    {γ:ℝ} (hγ:0<γ)
    (hP:∀c∈Icc (-1:ℝ) 1,fanLeft q K P N a b γ c<fanRight K P N a b c) : q.rate<1 := by
  apply polynomial_rate_lt_one q (familyLag K (P:=P) (N:=N)) (familyWeight a b)
  · intro i
    cases i with
    | inl m => change ((m.val*K+1:ℕ):ℤ)≠0; omega
    | inr m =>
      change -((m.val*K:ℕ):ℤ)≠0
      have hp:=Nat.mul_pos (hN _ m.property) (by omega : 0<K)
      omega
  · intro i
    cases i with
    | inl m => exact ha _ m.property
    | inr m => exact hb _ m.property
  · exact hγ
  · intro c hc
    rw [fan_polynomial_identity q (by omega) P N hN]
    exact sub_neg.mpr (hP c hc)

end polyak.Farey.Certificates
