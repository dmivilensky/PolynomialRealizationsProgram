import krylov.Methods.ProjectedResidual

/-!
Article: main_krylov, thm:UCq and thm:UCg, genuine uniform recorded-step control.
Use: Derive the true correction-to-total-step bound from the actual solve,
zero current search coordinate and normalized matrix/Gram conditioning.
Source: the exact original coefficient equation; a line search changes only
the new coefficient. Reuse the proved actual synthesis and coefficient Gram
bounds, including the empty earlier history and zero recorded movements.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Adding an exact zero new coordinate preserves the genuine Euclidean old-coefficient norm.
Use: Close the genuine relative-correction estimate needed by the source uniform spectral-gated RFC induction.
Article: main_krylov, thm:UCq and thm:UCg, uniform correction and recorded-step comparison.
Proof: The zero new solve coordinate bounds its head by its old tail; the line changes only the head, so the true Gram lower bound controls that tail through the recorded movement.
-/
theorem coefficient_zero_head_norm {p : ℕ} (c : Fin p → ℝ) :
    ‖WithLp.toLp 2 (Fin.cons 0 c : Fin (p+1) → ℝ)‖=‖WithLp.toLp 2 c‖ := by
  apply le_antisymm
  · have h := coordinate_norm_le_head_tail (Fin.cons 0 c : Fin (p+1) → ℝ)
    simpa only [Fin.cons_zero,Fin.cons_succ,abs_zero,zero_add] using h
  · simpa only [Fin.cons_succ] using coordinate_tail_norm_le (Fin.cons 0 c : Fin (p+1) → ℝ)

/-- A true model solve with zero new right-hand-side coordinate bounds every correction coefficient by its unchanged old tail.
Use: Close the genuine relative-correction estimate needed by the source uniform spectral-gated RFC induction.
Article: main_krylov, thm:UCq and thm:UCg, uniform correction and recorded-step comparison.
Proof: The zero new solve coordinate bounds its head by its old tail; the line changes only the head, so the true Gram lower bound controls that tail through the recorded movement.
-/
theorem zero_head_solve_coefficients {p : ℕ} (H : Matrix (Fin (p+1)) (Fin (p+1)) ℝ)
    (c : Fin (p+1) → ℝ) {a b : ℝ} (ha : 0<a) (hdiag : a≤H 0 0) (hH : ‖H‖≤b)
    (hc : (H*ᵥc) 0=0) :
    ‖WithLp.toLp 2 c‖≤(1+b/a)*‖WithLp.toLp 2 (fun i : Fin p => c i.succ)‖ := by
  -- The genuine first model row links the correction head to its old tail, which the line search leaves unchanged.
  let t : Fin p → ℝ := fun i => c i.succ
  let q : Fin (p+1) → ℝ := Fin.cons 0 t
  have hz : H 0 0*c 0+(H*ᵥq) 0=0 := by
    simpa only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,q,t,Fin.cons_zero,Fin.cons_succ,mul_zero,zero_add] using hc
  have he : |H 0 0*c 0|=|(H*ᵥq) 0| := by rw [eq_neg_of_add_eq_zero_left hz,abs_neg]
  have hq : ‖WithLp.toLp 2 q‖=‖WithLp.toLp 2 t‖ := coefficient_zero_head_norm t
  have hm := (Matrix.toEuclideanCLM (𝕜 := ℝ) H).le_opNorm (WithLp.toLp 2 q)
  rw [Matrix.l2_opNorm_toEuclideanCLM,hq] at hm
  have hp := PiLp.norm_apply_le ((Matrix.toEuclideanCLM (𝕜 := ℝ) H) (WithLp.toLp 2 q)) 0
  change |(H*ᵥq) 0|≤_ at hp
  have hH00 : 0≤H 0 0 := ha.le.trans hdiag
  have hh : a*|c 0|≤b*‖WithLp.toLp 2 t‖ := by
    calc
      _ ≤ H 0 0*|c 0| := mul_le_mul_of_nonneg_right hdiag (abs_nonneg _)
      _ = |(H*ᵥq) 0| := by rw [← abs_of_nonneg hH00,← abs_mul,he]
      _ ≤ b*‖WithLp.toLp 2 t‖ := hp.trans (hm.trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _)))
  have hhead : |c 0|≤b/a*‖WithLp.toLp 2 t‖ := by
    have hd : |c 0|≤(b*‖WithLp.toLp 2 t‖)/a := (le_div_iff₀ ha).mpr (by nlinarith)
    exact hd.trans_eq (by ring)
  exact (coordinate_norm_le_head_tail c).trans (by dsimp only [t] at hhead ⊢; nlinarith)

/-- The genuine model correction is uniformly bounded by its actual line-plus-correction total movement under true normalized matrix and Gram bounds.
Use: Close the genuine relative-correction estimate needed by the source uniform spectral-gated RFC induction.
Article: main_krylov, thm:UCq and thm:UCg, uniform correction and recorded-step comparison.
Proof: The zero new solve coordinate bounds its head by its old tail; the line changes only the head, so the true Gram lower bound controls that tail through the recorded movement.
-/
theorem correction_recorded_bound {p : ℕ} (s : Fin (p+1) → E)
    (H : Matrix (Fin (p+1)) (Fin (p+1)) ℝ) (c : Fin (p+1) → ℝ) (l : ℝ)
    {a b aG bG : ℝ} (ha : 0<a) (haG : 0<aG) (hbG : 0≤bG)
    (hdiag : a≤H 0 0) (hH : ‖H‖≤b) (hc : (H*ᵥc) 0=0)
    (hlower : ∀ i, aG≤(crossGram_isHermitian s).eigenvalues i)
    (hupper : ‖crossGram s s‖≤bG) :
    ‖combine s c‖≤(Real.sqrt bG*(1+b/a)*(Real.sqrt aG)⁻¹)*‖l • s 0+combine s c‖ := by
  -- The real recorded movement has exactly the same old coefficients as the solved correction; synthesize its genuine coefficient vector.
  let v : Fin (p+1) → ℝ := Fin.cons (l+c 0) (fun i => c i.succ)
  have hv : combine s v=l • s 0+combine s c := by
    simp only [combine,Fin.sum_univ_succ,v,Fin.cons_zero,Fin.cons_succ,add_smul]
    abel
  have ht : ‖WithLp.toLp 2 (fun i : Fin p => c i.succ)‖≤
      (Real.sqrt aG)⁻¹*‖l • s 0+combine s c‖ := by
    have h := (coordinate_tail_norm_le v).trans (combine_coefficients_bound s v haG hlower)
    rw [hv] at h
    simpa only [v,Fin.cons_succ] using h
  have hb : 0≤b := (norm_nonneg H).trans hH
  calc
    _ ≤ Real.sqrt bG*‖WithLp.toLp 2 c‖ := combine_norm_le s c hbG hupper
    _ ≤ Real.sqrt bG*((1+b/a)*‖WithLp.toLp 2 (fun i : Fin p => c i.succ)‖) :=
      mul_le_mul_of_nonneg_left (zero_head_solve_coefficients H c ha hdiag hH hc) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt bG*((1+b/a)*((Real.sqrt aG)⁻¹*‖l • s 0+combine s c‖)) := by
      gcongr
    _ = _ := by ring


/-- The actual original coefficient-model solve has a uniform correction-to-recorded-step bound whenever the true incoming search coordinate vanishes.
Use: Close the genuine relative-correction estimate needed by the source uniform spectral-gated RFC induction.
Article: main_krylov, thm:UCq and thm:UCg, uniform correction and recorded-step comparison.
Proof: The zero new solve coordinate bounds its head by its old tail; the line changes only the head, so the true Gram lower bound controls that tail through the recorded movement.
-/
theorem modelCorrection_recorded_bound {p : ℕ} (s : Fin (p+1) → E)
    (H : Matrix (Fin (p+1)) (Fin (p+1)) ℝ) (g : E) (l : ℝ)
    {a b aG bG : ℝ} (ha : 0<a) (haG : 0<aG) (hbG : 0≤bG)
    (hdiag : a≤H 0 0) (hH : ‖H‖≤b) (hu : IsUnit H.det) (horth : inner ℝ (s 0) g=0)
    (hlower : ∀ i, aG≤(crossGram_isHermitian s).eigenvalues i)
    (hupper : ‖crossGram s s‖≤bG) :
    ‖combine s (modelCoefficients s H g)‖≤(Real.sqrt bG*(1+b/a)*(Real.sqrt aG)⁻¹)*
      ‖l • s 0+combine s (modelCoefficients s H g)‖ := by
  have hc : (H*ᵥmodelCoefficients s H g) 0=0 := by
    rw [modelCoefficients,Matrix.mulVec_neg,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec]
    simp only [Pi.neg_apply,coordinates,horth,neg_zero]
  exact correction_recorded_bound s H _ l ha haG hbG hdiag hH hc hlower hupper

/-- The actual original raw correction and full recorded movement satisfy the uniform normalized conditioning bound without a minimum column length or an assumed relative-correction inequality.
Use: Close the genuine relative-correction estimate needed by the source uniform spectral-gated RFC induction.
Article: main_krylov, thm:UCq and thm:UCg, uniform correction and recorded-step comparison.
Proof: The zero new solve coordinate bounds its head by its old tail; the line changes only the head, so the true Gram lower bound controls that tail through the recorded movement.
-/
theorem normalizedCorrection_recorded_bound {p : ℕ} (s : Fin (p+1) → E)
    (H : Matrix (Fin (p+1)) (Fin (p+1)) ℝ) (g : E) (l : ℝ)
    (hs : ∀ i, s i≠0) {a b aG bG : ℝ} (ha : 0<a) (haG : 0<aG) (hbG : 0≤bG)
    (hdiag : a≤rescaleModel H (fun i => ‖s i‖⁻¹) 0 0)
    (hH : ‖rescaleModel H (fun i => ‖s i‖⁻¹)‖≤b)
    (hu : IsUnit (rescaleModel H (fun i => ‖s i‖⁻¹)).det) (horth : inner ℝ (s 0) g=0)
    (hlower : ∀ i, aG≤(crossGram_isHermitian (unitWindow s)).eigenvalues i)
    (hupper : ‖crossGram (unitWindow s) (unitWindow s)‖≤bG) :
    ‖combine s (modelCoefficients s H g)‖≤(Real.sqrt bG*(1+b/a)*(Real.sqrt aG)⁻¹)*
      ‖l • s 0+combine s (modelCoefficients s H g)‖ := by
  -- Normalize the true raw columns by their actual nonzero lengths, preserving both the correction and the full line-plus-correction movement exactly.
  let T := unitWindow s
  let Hn := rescaleModel H (fun i => ‖s i‖⁻¹)
  have hq := modelCorrection_rescale s H _ (unitWindow_diagonal_unit s hs) g
  change combine T (modelCoefficients T Hn g)=combine s (modelCoefficients s H g) at hq
  have horthn : inner ℝ (T 0) g=0 := by
    change inner ℝ (‖s 0‖⁻¹ • s 0) g=0
    rw [real_inner_smul_left,horth,mul_zero]
  have he : (l*‖s 0‖) • T 0=l • s 0 := by
    change (l*‖s 0‖) • (‖s 0‖⁻¹ • s 0)=_
    rw [smul_smul,mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hs 0)),mul_one]
  have hh := modelCorrection_recorded_bound T Hn g (l*‖s 0‖) ha haG hbG hdiag hH hu horthn hlower hupper
  rw [hq,he] at hh
  exact hh

end
end krylov.Correction
