import polyak.FareyPlateau.Ray.ThresholdDefinition

/-! The source adjacent two-lag symbol is an actual admissible competitor
in the unrestricted infimum, with exactly the stated weights. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set
open scoped BigOperators

def adjacentLag (n₁ : ℤ) (k : ℕ) : Fin 2→ℤ := ![n₁,n₁+k]
def adjacentWeight (t : ℝ) : Fin 2→ℝ := ![1-t,t]

theorem adjacent_gcd_one {j k : ℕ} {b n₁ : ℤ} (hb : (b*j)%k=1)
    (hn₁ : n₁%k=b%k) : Finset.univ.gcd (adjacentLag n₁ k)=1 := by
  let d := Finset.univ.gcd (adjacentLag n₁ k)
  have hd₁ : d∣n₁ := Finset.gcd_dvd (Finset.mem_univ (0:Fin 2))
  have hd₂ : d∣n₁+k := Finset.gcd_dvd (Finset.mem_univ (1:Fin 2))
  have hdk : d∣(k:ℤ) := by
    convert dvd_sub hd₂ hd₁ using 1; ring
  have hnmod := residue_product_one hb hn₁
  have hem := Int.emod_add_ediv_mul (n₁*j) (k:ℤ)
  rw [hnmod] at hem
  have hdj : d∣n₁*j := dvd_mul_of_dvd_left hd₁ _
  have hdm : d∣(n₁*j/k)*(k:ℤ) := dvd_mul_of_dvd_right hdk _
  have hd : d∣(1:ℤ) := by
    convert dvd_sub hdj hdm using 1
    nlinarith only [hem]
  have hnorm : normalize d=d := Finset.normalize_gcd
  exact hnorm.symm.trans (normalize_eq_one.mpr (isUnit_iff_dvd_one.mpr hd))

def adjacentCertificate {j k : ℕ} {b n₁ : ℤ} {D t : ℝ}
    (hk : 0<k) (hb : (b*j)%k=1) (hn₁ : n₁%k=b%k) (ht0 : 0<t) (ht1 : t<1)
    (hbar : edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D=(n₁:ℝ)+t*k) :
    SourceCertificate j k b D where
  card := 2
  lag := adjacentLag n₁ k
  weight := adjacentWeight t
  admissible := by
    have hclass (i : Fin 2) : adjacentLag n₁ k i%k=b%k := by
      fin_cases i
      · exact hn₁
      · change (n₁+(k:ℤ))%k=b%k
        rw [Int.add_emod_right]
        exact hn₁
    have hnonzero (i : Fin 2) : adjacentLag n₁ k i≠0 := by
      intro hh
      have he := hclass i
      rw [hh,Int.zero_emod] at he
      exact inverse_residue_nonzero hb he.symm
    refine ⟨?_,hnonzero,?_,?_,fun i=>Or.inl (hclass i),?_,adjacent_gcd_one hb hn₁,?_⟩
    · intro i l he
      fin_cases i <;> fin_cases l
      · rfl
      · have hh : n₁=n₁+k := he; omega
      · have hh : n₁+k=n₁ := he; omega
      · rfl
    · intro i;fin_cases i
      · exact sub_pos.mpr ht1
      · exact ht0
    · simp only [adjacentWeight,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
      ring
    · exact ⟨0,1,by change n₁≠n₁+k;omega,hclass 0,hclass 1⟩
    · have hOne : Finset.univ.filter (fun i : Fin 2=>adjacentLag n₁ k i%k=b%k)=Finset.univ := by
        apply Finset.filter_eq_self.mpr; intro i _; exact hclass i
      have hZero : Finset.univ.filter (fun i : Fin 2=>adjacentLag n₁ k i%k=0)=∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i _ hz
        rw [hclass i] at hz
        exact inverse_residue_nonzero hb hz
      rw [hOne,hZero,Finset.sum_empty,hbar]
      simp only [adjacentLag,adjacentWeight,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
        Int.cast_add,Int.cast_natCast]
      ring

end polyak.FareyPlateau.Ray
