import krylov.Correction.ThreeDirectionWitness

/-!
Article: main_krylov, thm:C2(b), the genuine CG three-direction witness.
Use: realize the double-correction cubic coefficient on the actual source
old flags and fresh defect, with the required first two zero increments.
Source: the proved three-direction physical matrix and the actual active
orthonormal CG frame, including the source chronological increment cutoff.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Reference krylov.Variation krylov.Envelope krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The actual source witness increments in its genuine first, second and terminal CG directions.
Use: all increments before index two vanish exactly.
Article: main_krylov, thm:C2(b), Ê_l=ω_lN for l≥2. -/
def threeDirectionIncrements (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (ω : ℕ → ℝ) (a b : ℝ) :
    ℕ → Matrix (Fin n) (Fin n) ℝ := fun i =>
  if 2 ≤ i then ω i • threeDirectionMatrix (canonicalCGUnitStep base g 0)
    (canonicalCGUnitStep base g 1) (canonicalCGUnitStep base g (N-1)) a b else 0

/-- The source three-direction witness has its exact cubic double-staircase vector in the actual CG frame.
Use: the lower coefficient is computed on the genuine article geometry, without an abstract chosen flag.
Article: main_krylov, thm:C2(b), 𝓛²f̂=ab²W₀³ŝ₀ when ω₀=ω₁=ω′=0.
Proof: actual CG orthonormality supplies the three genuine orthonormal
directions. Every relevant true old flag contains the first two and is
orthogonal to the terminal one. Remove the exactly zero first increments
from the actual sums, then apply the proved physical double-action identity.
-/
theorem threeDirection_reference_value (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g) (hfour : 4≤N)
    (ω : ℕ → ℝ) (a b : ℝ) :
    let D := threeDirectionIncrements base g N ω a b
    let L := staircaseOperator base g D 0 N
    L (L (freshDefect base g D N))=
      (a*b^2*(∑ i∈Ico 2 (N-1), ω i)^3) • canonicalCGUnitStep base g 0 := by
  -- Derive every true witness pairing and old-flag membership from actual CG.
  let e := canonicalCGUnitStep base g 0
  let v := canonicalCGUnitStep base g 1
  let f := canonicalCGUnitStep base g (N-1)
  let D := threeDirectionIncrements base g N ω a b
  let M := threeDirectionMatrix e v f a b
  let I := Ico 2 (N-1)
  have ho := canonicalCGUnitStep_orthonormal base hb g N
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hN))
  have he : ‖e‖=1 := by simpa only [e,Fin.val_mk] using ho.norm_eq_one ⟨0,by omega⟩
  have hv : ‖v‖=1 := by simpa only [v,Fin.val_mk] using ho.norm_eq_one ⟨1,by omega⟩
  have hf : ‖f‖=1 := by simpa only [f,Fin.val_mk] using ho.norm_eq_one ⟨N-1,by omega⟩
  have hev : inner ℝ e v=0 := by
    simpa only [e,v,Fin.val_mk] using (ho.inner_eq_zero
      (show (⟨0,by omega⟩ : Fin N)≠⟨1,by omega⟩ from by
        intro h; have hval : (0 : ℕ)=1 := congrArg Fin.val h; omega))
  have hef : inner ℝ e f=0 := by
    simpa only [e,f,Fin.val_mk] using (ho.inner_eq_zero
      (show (⟨0,by omega⟩ : Fin N)≠⟨N-1,by omega⟩ from by
        intro h; have hval : (0 : ℕ)=N-1 := congrArg Fin.val h; omega))
  have hvf : inner ℝ v f=0 := by
    simpa only [v,f,Fin.val_mk] using (ho.inner_eq_zero
      (show (⟨1,by omega⟩ : Fin N)≠⟨N-1,by omega⟩ from by
        intro h; have hval : (1 : ℕ)=N-1 := congrArg Fin.val h; omega))
  have hsub : I⊆range (N-1) := fun i hi => mem_range.mpr (mem_Ico.mp hi).2
  have hD (i : ℕ) (hi : i∈I) : D i=ω i • M := ite_eq_left (mem_Ico.mp hi).1
  have hz (i : ℕ) (hi : i∈range (N-1)) (hni : i∉I) : D i=0 := by
    have hnot : ¬ 2 ≤ i := by intro h; exact hni (mem_Ico.mpr ⟨h,mem_range.mp hi⟩)
    exact ite_eq_right hnot
  -- Restrict both actual finite sums to precisely the nonzero source range.
  have hr : freshDefect base g D N=
      ∑ i∈I, (oldFlag base g i).starProjection (cgOperator (ω i • M) f) := by
    unfold freshDefect
    rw [← sum_subset hsub (fun i hi hni => by rw [hz i hi hni]; simp only [cgOperator,map_zero,_root_.zero_apply,map_zero])]
    exact sum_congr rfl fun i hi => by rw [hD i hi]
  have hL : staircaseOperator base g D 0 N=
      ∑ i∈I, (oldFlag base g i).starProjection*cgOperator (ω i • M)*(oldFlag base g i).starProjection := by
    simp only [staircaseOperator,cgOperator,map_zero,add_zero]
    rw [← sum_subset hsub (fun i hi hni => by rw [hz i hi hni]; simp only [map_zero,mul_zero,zero_mul])]
    exact sum_congr rfl fun i hi => by rw [hD i hi]
  change staircaseOperator base g D 0 N (staircaseOperator base g D 0 N (freshDefect base g D N))=_
  rw [hL,hr]
  exact threeDirection_double_value I (oldFlag base g) e v f he hv hf hev hef hvf
    (fun i hi => unitStep_mem_oldFlag base g (by have := (mem_Ico.mp hi).1; omega))
    (fun i hi => unitStep_mem_oldFlag base g (by have := (mem_Ico.mp hi).1; omega))
    (fun i hi => unitStep_prefix_oldFlag_orthogonal base hb g hN (by omega) (mem_Ico.mp hi).2)
    ω a b

/-- The actual CG witness satisfies all individual source budgets and attains the source double-correction cubic norm.
Use: the three-dimensional coefficient is attained for every nonnegative profile with its first two budgets zero.
Article: main_krylov, thm:C2(b), 2W₀³/(3√3) on genuine CG flags.
Proof: choose the proved maximizing a and its unit-circle complement b.
Actual CG orthonormality proves the real matrix's spectral budget. Its first
two increments vanish; the corresponding zero profile entries identify the
remaining total with W₀. The actual double-action formula and the exact
scalar maximizer give the stated norm, including the zero-total case.
-/
theorem threeDirection_reference_attained (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g) (hfour : 4≤N)
    (ω : ℕ → ℝ) (hω : ∀ i∈range (N-1), 0≤ω i) (hω0 : ω 0=0) (hω1 : ω 1=0) :
    let D := threeDirectionIncrements base g N ω cubicMaximizer (Real.sqrt (1-cubicMaximizer^2))
    D 0=0 ∧ D 1=0 ∧ (∀ i, (D i).IsSymm) ∧ (∀ i∈range (N-1), ‖D i‖≤ω i) ∧
      ‖staircaseOperator base g D 0 N
        (staircaseOperator base g D 0 N (freshDefect base g D N))‖=
          2/(3*Real.sqrt 3)*(∑ i∈range (N-1), ω i)^3 := by
  -- Use the same concrete actual matrix for its budgets and its final coefficient.
  let a := cubicMaximizer
  let b := Real.sqrt (1-a^2)
  let D := threeDirectionIncrements base g N ω a b
  have ha : 0<a := cubicMaximizer_spec.1
  have hb₂ : b^2=1-a^2 := Real.sq_sqrt (by dsimp only [a]; rw [cubicMaximizer_spec.2.2]; norm_num)
  have hab : a^2+b^2=1 := by linarith
  have ho := canonicalCGUnitStep_orthonormal base hb g N
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hN))
  have hn (j : ℕ) (hj : j<N) : ‖canonicalCGUnitStep base g j‖=1 := by
    simpa only [Fin.val_mk] using ho.norm_eq_one ⟨j,hj⟩
  have hp (i j : ℕ) (hi : i<N) (hj : j<N) (hne : i≠j) :
      inner ℝ (canonicalCGUnitStep base g i) (canonicalCGUnitStep base g j)=0 := by
    simpa only [Fin.val_mk] using (ho.inner_eq_zero
      (show (⟨i,hi⟩ : Fin N)≠⟨j,hj⟩ from fun h => hne (congrArg Fin.val h)))
  have hM := threeDirectionMatrix_budget (canonicalCGUnitStep base g 0)
    (canonicalCGUnitStep base g 1) (canonicalCGUnitStep base g (N-1))
    (hn 0 (by omega)) (hn 1 (by omega)) (hn (N-1) (by omega))
    (hp 0 1 (by omega) (by omega) (by omega))
    (hp 0 (N-1) (by omega) (by omega) (by omega))
    (hp 1 (N-1) (by omega) (by omega) (by omega)) a b hab
  have hsym (i : ℕ) : (D i).IsSymm := by
    dsimp only [D,threeDirectionIncrements]
    split_ifs
    · exact hM.1.smul _
    · exact Matrix.isSymm_zero
  refine ⟨rfl,rfl,hsym,?_,?_⟩
  · intro i hi
    dsimp only [D,threeDirectionIncrements]
    split_ifs
    · rw [norm_smul,Real.norm_of_nonneg (hω i hi)]
      exact (mul_le_mul_of_nonneg_left hM.2 (hω i hi)).trans_eq (mul_one _)
    · simpa only [norm_zero] using hω i hi
  · have hsum : (∑ i∈Ico 2 (N-1), ω i)=∑ i∈range (N-1), ω i := by
      apply sum_subset (fun i hi => mem_range.mpr (mem_Ico.mp hi).2)
      intro i hi hni
      have hsmall : i<2 := by
        have hr := mem_range.mp hi
        simp only [mem_Ico,not_and] at hni
        omega
      rcases (by omega : i=0 ∨ i=1) with rfl | rfl
      · exact hω0
      · exact hω1
    rw [threeDirection_reference_value base hb g hN hfour ω a b,norm_smul,Real.norm_eq_abs,
      hn 0 (by omega),mul_one,
      abs_of_nonneg (mul_nonneg (mul_nonneg ha.le (sq_nonneg b))
        (pow_nonneg (sum_nonneg fun i hi => hω i (mem_range.mpr (mem_Ico.mp hi).2)) 3)),hsum]
    rw [mul_assoc,hb₂,← mul_assoc,cubic_tradeoff_attained]

end
end krylov.Correction
