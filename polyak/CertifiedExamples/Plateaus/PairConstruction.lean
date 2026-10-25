import polyak.CertifiedExamples.Plateaus.CoordinateCode

/-! Exact construction of a pinned dual from a left kernel and a polynomial
first-jet linear system. The support equalities are never tested numerically. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels Matrix
open scoped BigOperators

def pairLag {d : ℕ} (n₁ n₂ : Fin d → ℤ) (p : Fin d × Fin 2) : ℤ :=
  if p.2=0 then n₁ p.1 else n₂ p.1

def pairWeight {d : ℕ} (μ m : Fin d → ℝ) (p : Fin d × Fin 2) : ℝ :=
  if p.2=0 then μ p.1-m p.1 else m p.1

def pairSlope {d : ℕ} (X : Fin 3 → ℝ) (n₁ n₂ : Fin d → ℤ)
    (c : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i r =>
  coordinateCodeValue X (n₂ r) 1 (c i)-coordinateCodeValue X (n₁ r) 1 (c i)

def pairTarget {d : ℕ} (X : Fin 3 → ℝ) (n₁ : Fin d → ℤ)
    (c μ : Fin d → ℝ) : Fin d → ℝ := fun i =>
  -(∑ r,μ r*coordinateCodeValue X (n₁ r) 1 (c i))

def pairMoments {d : ℕ} (X : Fin 3 → ℝ) (n₁ n₂ : Fin d → ℤ)
    (c μ : Fin d → ℝ) : Fin d → ℝ :=
  slopeMoments (pairSlope X n₁ n₂ c) (pairTarget X n₁ c μ)

theorem pairWeight_sum {d : ℕ} (μ m : Fin d → ℝ) :
    (∑ p:Fin d×Fin 2,pairWeight μ m p)=∑i,μ i := by
  simp only [Fintype.sum_prod_type,pairWeight,Fin.sum_univ_two]
  apply Finset.sum_congr rfl
  intro i _
  norm_num

theorem pair_value_zero {d : ℕ} (X : Fin 3 → ℝ) (n₁ n₂ : Fin d → ℤ)
    (c μ m : Fin d → ℝ)
    (hμ : ∀ i,(∑ r,μ r*coordinateLag X (n₁ r) (c i))=0)
    (hp : ∀ i r,coordinateLag X (n₂ r) (c i)=coordinateLag X (n₁ r) (c i))
    (i : Fin d) :
    (∑ p:Fin d×Fin 2,pairWeight μ m p*coordinateLag X (pairLag n₁ n₂ p) (c i))=0 := by
  simp only [Fintype.sum_prod_type,pairWeight,pairLag,Fin.sum_univ_two]
  simp only [ite_true,show (1:Fin 2)≠0 by decide,ite_false]
  simp_rw [hp]
  have he : (∑ r,((μ r-m r)*coordinateLag X (n₁ r) (c i)+
      m r*coordinateLag X (n₁ r) (c i)))=
      ∑ r,μ r*coordinateLag X (n₁ r) (c i) := by
    apply Finset.sum_congr rfl
    intro r _
    ring
  exact he.trans (hμ i)

theorem pair_first_jet_zero {d : ℕ} (X : Fin 3 → ℝ) (n₁ n₂ : Fin d → ℤ)
    (c μ : Fin d → ℝ) (hV : (pairSlope X n₁ n₂ c).det≠0) (i : Fin d) :
    (∑ p:Fin d×Fin 2,pairWeight μ (pairMoments X n₁ n₂ c μ) p*
      coordinateCodeValue X (pairLag n₁ n₂ p) 1 (c i))=0 := by
  have hs := congrFun
    (slopeMoments_solve (pairSlope X n₁ n₂ c) (pairTarget X n₁ c μ) hV) i
  change (∑ r,(coordinateCodeValue X (n₂ r) 1 (c i)-
      coordinateCodeValue X (n₁ r) 1 (c i))*pairMoments X n₁ n₂ c μ r)=
      -(∑ r,μ r*coordinateCodeValue X (n₁ r) 1 (c i)) at hs
  simp only [Fintype.sum_prod_type,pairWeight,pairLag,Fin.sum_univ_two]
  simp only [ite_true,show (1:Fin 2)≠0 by decide,ite_false]
  have he : (∑ r,((μ r-pairMoments X n₁ n₂ c μ r)*coordinateCodeValue X (n₁ r) 1 (c i)+
      pairMoments X n₁ n₂ c μ r*coordinateCodeValue X (n₂ r) 1 (c i)))=
      (∑ r,μ r*coordinateCodeValue X (n₁ r) 1 (c i))+
      ∑ r,(coordinateCodeValue X (n₂ r) 1 (c i)-coordinateCodeValue X (n₁ r) 1 (c i))*
        pairMoments X n₁ n₂ c μ r := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he,hs,add_neg_cancel]

end polyak.CertifiedExamples.Plateaus
