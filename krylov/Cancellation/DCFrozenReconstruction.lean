import krylov.Stability.FixedBasisOrder
import krylov.Cancellation.DeferredResponse
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), exact true fresh-coordinate reconstruction.
Use: represent all frozen physical fresh coordinates in the genuine full
reference basis and identify the original calibrated canonical response.
Source: proved actual full-basis inverse, true CG independence and the
already proved literal deferred physical coordinate identities.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation krylov.Correction
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual full reference-basis reconstruction of the frozen newest
physical defect coordinates.
Use: compact C-one cycle estimates retain the real operator differences
while their two outer step vectors are genuinely frozen at the reference.
Article: main_krylov, apH:dcs2(b), full frozen fresh physical gradient. -/
def frozenFreshGradient (s : Fin n → EuclideanSpace ℝ (Fin n))
    (step : EuclideanSpace ℝ (Fin n))
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  cgOperator ((fullBasisMatrix s)ᵀ)⁻¹
    (WithLp.toLp 2 (fun i => inner ℝ (s i) ((A k-A i.val) step)))

/-- The reconstructed vector has exactly the real frozen fresh coordinates
on every genuine full independent physical reference basis.
Use: reference inverse domains follow from actual independence.
Article: main_krylov, apH:dcs2(b), exact full fresh reconstruction coordinates.
Proof: the real full reference column matrix is nonsingular; its transpose
cancels the actual inverse transpose acting on the true finite pairing vector. -/
theorem frozen_fresh_gradient_coordinates (s : Fin n → EuclideanSpace ℝ (Fin n))
    (hs : LinearIndependent ℝ s) (step : EuclideanSpace ℝ (Fin n))
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) (i : Fin n) :
    inner ℝ (s i) (frozenFreshGradient s step A k)=inner ℝ (s i) ((A k-A i.val) step) := by
  let c := WithLp.toLp 2 (fun i : Fin n => inner ℝ (s i) ((A k-A i.val) step))
  have hu : IsUnit ((fullBasisMatrix s)ᵀ).det := by simpa only [det_transpose] using fullBasisMatrix_unit s hs
  have he : projectedResidual s (frozenFreshGradient s step A k)=c := by
    rw [projectedResidual_fullBasisMatrix]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (fullBasisMatrix s)ᵀ
      (Matrix.toEuclideanCLM (𝕜 := ℝ) ((fullBasisMatrix s)ᵀ)⁻¹ c)=c
    rw [← mul_apply_eq_comp,← map_mul,mul_nonsing_inv _ hu,map_one,one_apply_eq_self]
  exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) he

/-- On the original canonical source matrices the true full physical fresh
reconstruction is exactly the calibrated deferred canonical response.
Use: compact C-one physical cycle reconstruction has the literal source
response, not an independently supplied surrogate vector.
Article: main_krylov, apH:dcs2(b), original full fresh response dictionary.
Proof: the genuine full CG physical basis is independent. Its exact real
frozen coordinates match the proved calibrated deferred coordinates after
the true positive-root pairing; the full canonical CG basis separates vectors. -/
theorem frozen_fresh_gradient_canonical (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hcount : referenceAtomCount base hb g=n) (hfull : k+1=n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    cgOperator (metricRoot base)⁻¹
      (frozenFreshGradient (fun i : Fin n => referenceStep (cgOperator base) g i.val)
        (referenceStep (cgOperator base) g k) (canonicalFCPath base E 1) k)=deferredResponse base g k 0 E := by
  let Q := cgOperator base
  let s := fun i : Fin n => referenceStep Q g i.val
  let F := frozenFreshGradient s (referenceStep Q g k) (canonicalFCPath base E 1) k
  have hN : k+1≤referenceAtomCount base hb g := by omega
  have hs : LinearIndependent ℝ s := reference_window_independent Q (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g n (fun j hj => cg_nonstagnation base hb g j (by omega))
    (fun i : Fin n => i.val) Fin.val_injective (fun i => i.isLt)
  apply canonical_step_inner_ext base hb g hcount
  intro i hi
  have hc := frozen_fresh_gradient_coordinates s hs (referenceStep Q g k) (canonicalFCPath base E 1) k ⟨i,hi⟩
  have hmetric : inner ℝ (canonicalCGStep base g i) (cgOperator (metricRoot base)⁻¹ F)=
      inner ℝ (referenceStep Q g i) F := (canonical_search_pairing base hb _ _).symm
  change inner ℝ (canonicalCGStep base g i) (cgOperator (metricRoot base)⁻¹ F)=_
  rw [hmetric]
  by_cases hik : i<k
  · rw [deferred_response_physical_coordinates base hb g k hN 0 E i hik,zero_mul,zero_add]
    have hT : canonicalFCPath base E 1 k-canonicalFCPath base E 1 i=
        cumulativeDrift base E k-cumulativeDrift base E i := by
      simp only [canonicalFCPath,one_smul]
      abel
    rw [hT] at hc
    exact hc
  · have he : i=k := by omega
    subst i
    rw [deferred_response_last_coordinate base hb g k hN 0 E]
    simpa only [sub_self,_root_.zero_apply,inner_zero_right] using hc

end
end krylov.Cancellation
