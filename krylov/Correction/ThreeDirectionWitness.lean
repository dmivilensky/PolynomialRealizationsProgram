import krylov.Correction.RepeatedBound
import krylov.Correction.InformedScalar

/-!
Article: main_krylov, thm:C2(b), the three-direction RFC₂ witness.
Use: construct the actual symmetric budget matrices and compute their double
staircase action, including zero and empty profiles.
Source: the printed rank-two operator coupling e with af+bv; reuse the proved
planar spectral bound rather than asserting a characteristic polynomial.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Reference krylov.Variation krylov.Envelope krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {ι : Type*} {n : ℕ}

/-- The source three-direction perturbation, represented by its actual rank-two matrix.
Use: e couples to both the terminal direction f and the second old direction v.
Article: main_krylov, thm:C2(b), N=a(feᵀ+efᵀ)+b(evᵀ+veᵀ). -/
def threeDirectionMatrix (e v f : EuclideanSpace ℝ (Fin n)) (a b : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := planarMatrix e (a • f+b • v) 0 1 0

/-- The actual three-direction matrix is symmetric and satisfies the unit spectral budget.
Use: the witness's primitive admissibility follows from its real physical matrix.
Article: main_krylov, thm:C2(b), ‖N‖≤1 when a²+b²=1.
Proof: af+bv is a unit vector perpendicular to e. The existing rank-two
planar spectral estimate applies with zero diagonal and unit cross entry. -/
theorem threeDirectionMatrix_budget (e v f : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hv : ‖v‖=1) (hf : ‖f‖=1)
    (hev : inner ℝ e v=0) (hef : inner ℝ e f=0) (hvf : inner ℝ v f=0)
    (a b : ℝ) (hab : a^2+b^2=1) :
    (threeDirectionMatrix e v f a b).IsSymm ∧ ‖threeDirectionMatrix e v f a b‖≤1 := by
  -- The apparent three-dimensional matrix is a planar operator in the rotated hidden direction.
  let q := a • f+b • v
  have hff : inner ℝ f f=1 := by rw [real_inner_self_eq_norm_sq,hf,one_pow]
  have hvv : inner ℝ v v=1 := by rw [real_inner_self_eq_norm_sq,hv,one_pow]
  have hfv : inner ℝ f v=0 := by rw [real_inner_comm]; exact hvf
  have hq : ‖q‖=1 := by
    have hqq : inner ℝ q q=1 := by
      simp only [q,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
        hff,hvv,hvf,hfv,mul_one,mul_zero,add_zero,zero_add]
      nlinarith [hab]
    rw [real_inner_self_eq_norm_sq] at hqq
    nlinarith [norm_nonneg q]
  have heq : inner ℝ e q=0 := by
    simp only [q,inner_add_right,real_inner_smul_right,hef,hev,mul_zero,add_zero]
  refine ⟨planarMatrix_isSymm _ _ _ _ _,?_⟩
  simpa only [neg_zero,threeDirectionMatrix,q,chebyshev1.opNorm] using
    planar_spectral_norm_le e q he hq heq 0 1 (by norm_num)

/-- The three true witness directions have the exact physical actions Nf=ae, Ne=af+bv and Nv=be.
Use: evaluate the full compressed double correction on the actual matrices.
Article: main_krylov, thm:C2(b), three-direction action identities.
Proof: evaluate the proved planar matrix action and the genuine orthonormal
pairings of e,v,f; no spectral-coordinate assumption is introduced. -/
theorem threeDirectionMatrix_actions (e v f : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hv : ‖v‖=1) (hf : ‖f‖=1)
    (hev : inner ℝ e v=0) (hef : inner ℝ e f=0) (hvf : inner ℝ v f=0) (a b : ℝ) :
    cgOperator (threeDirectionMatrix e v f a b) f=a • e ∧
      cgOperator (threeDirectionMatrix e v f a b) e=a • f+b • v ∧
      cgOperator (threeDirectionMatrix e v f a b) v=b • e := by
  -- Evaluate all three real columns using the same orthonormal pairings.
  have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he,one_pow]
  have hvv : inner ℝ v v=1 := by rw [real_inner_self_eq_norm_sq,hv,one_pow]
  have hff : inner ℝ f f=1 := by rw [real_inner_self_eq_norm_sq,hf,one_pow]
  have hve : inner ℝ v e=0 := by rw [real_inner_comm]; exact hev
  have hfe : inner ℝ f e=0 := by rw [real_inner_comm]; exact hef
  have hfv : inner ℝ f v=0 := by rw [real_inner_comm]; exact hvf
  simp only [threeDirectionMatrix,cgOperator,planarMatrix_action,inner_add_left,
    real_inner_smul_left,hee,hvv,hff,hev,hef,hvf,hve,hfe,hfv,mul_one,mul_zero,
    zero_mul,zero_smul,one_smul,one_mul,add_zero,zero_add,and_self]

/-- Budget-scaled three-direction matrices have the exact source double-compression coefficient.
Use: certify the same actual matrices' individual budgets and full cubic residual.
Article: main_krylov, thm:C2(b), 𝓛²f̂=ab²W³e.
Proof: every old projector fixes e,v and annihilates f. Consequently the
fresh vector is aWe, the compressed operator sends e to bWv and v to bWe.
Linearity of the actual finite sums gives the stated double action.
-/
theorem threeDirection_double_value (I : Finset ι)
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) [∀ i, (K i).HasOrthogonalProjection]
    (e v f : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hv : ‖v‖=1) (hf : ‖f‖=1)
    (hev : inner ℝ e v=0) (hef : inner ℝ e f=0) (hvf : inner ℝ v f=0)
    (heK : ∀ i∈I, e∈K i) (hvK : ∀ i∈I, v∈K i) (hfK : ∀ i∈I, f∈(K i)ᗮ)
    (ω : ι → ℝ) (a b : ℝ) :
    let D := fun i => ω i • threeDirectionMatrix e v f a b
    let T := fun i => cgOperator (D i)
    let R := ∑ i∈I, (K i).starProjection (T i f)
    let L := ∑ i∈I, (K i).starProjection*T i*(K i).starProjection
    L (L R)=(a*b^2*(∑ i∈I, ω i)^3) • e := by
  -- Work with the actual physical operator and its projected finite sum.
  let N := cgOperator (threeDirectionMatrix e v f a b)
  let T := fun i => cgOperator (ω i • threeDirectionMatrix e v f a b)
  let L := ∑ i∈I, (K i).starProjection*T i*(K i).starProjection
  let W := ∑ i∈I, ω i
  obtain ⟨hNf,hNe,hNv⟩ := threeDirectionMatrix_actions e v f he hv hf hev hef hvf a b
  change N f=a • e at hNf
  change N e=a • f+b • v at hNe
  change N v=b • e at hNv
  have hPe (i : ι) (hi : i∈I) : (K i).starProjection e=e :=
    (K i).starProjection_eq_self_iff.mpr (heK i hi)
  have hPv (i : ι) (hi : i∈I) : (K i).starProjection v=v :=
    (K i).starProjection_eq_self_iff.mpr (hvK i hi)
  have hPf (i : ι) (hi : i∈I) : (K i).starProjection f=0 :=
    (K i).starProjection_apply_eq_zero_iff.mpr (hfK i hi)
  have hT (i : ι) (x : EuclideanSpace ℝ (Fin n)) : T i x=ω i • N x := by
    simp only [T,N,cgOperator,map_smul,_root_.smul_apply]
  have hR : (∑ i∈I, (K i).starProjection (T i f))=(W*a) • e := by
    calc
      _ = ∑ i∈I, (ω i*a) • e := sum_congr rfl fun i hi => by rw [hT,hNf,map_smul,map_smul,hPe i hi,smul_smul]
      _ = _ := by rw [← sum_smul,← sum_mul]
  have hLe : L e=(W*b) • v := by
    change (∑ i∈I, (K i).starProjection*T i*(K i).starProjection) e=_
    rw [_root_.sum_apply]
    calc
      _ = ∑ i∈I, (ω i*b) • v := sum_congr rfl fun i hi => by
        simp only [mul_apply_eq_comp,hPe i hi,hT,hNe,map_smul,map_add,hPf i hi,hPv i hi,
          smul_zero,zero_add,smul_smul]
      _ = _ := by rw [← sum_smul,← sum_mul]
  have hLv : L v=(W*b) • e := by
    change (∑ i∈I, (K i).starProjection*T i*(K i).starProjection) v=_
    rw [_root_.sum_apply]
    calc
      _ = ∑ i∈I, (ω i*b) • e := sum_congr rfl fun i hi => by
        simp only [mul_apply_eq_comp,hPv i hi,hT,hNv,map_smul,hPe i hi,smul_smul]
      _ = _ := by rw [← sum_smul,← sum_mul]
  change L (L (∑ i∈I, (K i).starProjection (T i f)))=_
  rw [hR,map_smul,hLe,map_smul,map_smul,hLv]
  simp only [smul_smul]
  congr 1
  ring

/-- Actual symmetric three-direction matrices attain the source cubic double-correction constant.
Use: the exact coefficient 2/(3√3) is realized within every individual spectral budget.
Article: main_krylov, thm:C2(b), three-dimensional lower witness.
Proof: choose a=1/√3 and b=√(1−a²). The proved real matrix satisfies the
unit spectral budget; scale it by each nonnegative profile entry. Its actual
double action has norm ab²W³, and the proved scalar maximizer gives the value.
-/
theorem threeDirection_double_attained (I : Finset ι)
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) [∀ i, (K i).HasOrthogonalProjection]
    (e v f : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hv : ‖v‖=1) (hf : ‖f‖=1)
    (hev : inner ℝ e v=0) (hef : inner ℝ e f=0) (hvf : inner ℝ v f=0)
    (heK : ∀ i∈I, e∈K i) (hvK : ∀ i∈I, v∈K i) (hfK : ∀ i∈I, f∈(K i)ᗮ)
    (ω : ι → ℝ) (hω : ∀ i∈I, 0≤ω i) :
    ∃ D : ι → Matrix (Fin n) (Fin n) ℝ,
      (∀ i∈I, (D i).IsSymm ∧ ‖D i‖≤ω i) ∧
      let T := fun i => cgOperator (D i)
      let R := ∑ i∈I, (K i).starProjection (T i f)
      let L := ∑ i∈I, (K i).starProjection*T i*(K i).starProjection
      ‖L (L R)‖=2/(3*Real.sqrt 3)*(∑ i∈I, ω i)^3 := by
  -- The same concrete matrices establish both primitive budgets and the attained action.
  let a := cubicMaximizer
  let b := Real.sqrt (1-a^2)
  have ha : 0<a := cubicMaximizer_spec.1
  have hb : 0≤b := Real.sqrt_nonneg _
  have hb₂ : b^2=1-a^2 := Real.sq_sqrt (by dsimp only [a]; rw [cubicMaximizer_spec.2.2]; norm_num)
  have hab : a^2+b^2=1 := by linarith
  have hN := threeDirectionMatrix_budget e v f he hv hf hev hef hvf a b hab
  let D := fun i => ω i • threeDirectionMatrix e v f a b
  refine ⟨D,?_,?_⟩
  · intro i hi
    refine ⟨hN.1.smul _,?_⟩
    rw [norm_smul,Real.norm_of_nonneg (hω i hi)]
    exact (mul_le_mul_of_nonneg_left hN.2 (hω i hi)).trans_eq (mul_one _)
  · have hvalue := threeDirection_double_value I K e v f he hv hf hev hef hvf heK hvK hfK ω a b
    dsimp only at hvalue ⊢
    rw [hvalue,norm_smul,Real.norm_eq_abs,he,mul_one,
      abs_of_nonneg (mul_nonneg (mul_nonneg ha.le (sq_nonneg b)) (pow_nonneg (sum_nonneg hω) 3))]
    rw [mul_assoc,hb₂,← mul_assoc,cubic_tradeoff_attained]

end
end krylov.Correction
