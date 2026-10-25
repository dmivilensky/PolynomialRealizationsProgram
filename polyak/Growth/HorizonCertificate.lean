import polyak.Energy.Estimate
import polyak.Growth.HorizonPlateau

/-!
Article: Appendix C, a finite certificate uses only its finitely many lags.
Use: its energy estimate holds for every actual finite-memory H-table once all
certificate lags are retained. Values at the unused index zero are extended by zero.
The recurrence and every interpolation sign are proved from the H-table itself.
-/

namespace polyak.Growth.FiniteHorizon
noncomputable section
open Energy Interpolation Duality Spectral Growth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A B β : ℝ} {H : ℕ}

/-- Only positive indices carry sampled values in an H-table. -/
def sampleValue (r : HRun E A B β H) (k : ℕ) : ℝ := if k=0 then 0 else r.value k

theorem sampleValue_eq (r : HRun E A B β H) {k : ℕ} (hk : 1 ≤ k) :
    sampleValue r k=r.value k := by simp [sampleValue,show k≠0 by omega]

/-- Both pair signs follow from a retained actual interpolation pair. -/
theorem _root_.polyak.Growth.HRun.discounted_pair_nonneg (r : HRun E A B β H) (t δ : ℝ)
    (hδ : δ=1 ∨ δ= -1) (k n : ℕ) (hk : 1 ≤ k) (hn : n ≤ H) :
    0 ≤ pairQuadratic δ (discountedPosition r.x t k)
      (Real.exp (n*t) • discountedPosition r.x t (k+n))
      (discountedPosition r.σ t k) (Real.exp (n*t) • discountedPosition r.σ t (k+n)) +
      δ*(Real.exp (2*n*t)*discountedValue (sampleValue r) t (k+n)-
        discountedValue (sampleValue r) t k) := by
  rw [discounted_pair_slack]
  apply mul_nonneg (Real.exp_pos _).le
  have hh := abs_le.mp (r.interpolation k hk (k+n) (by omega)
    (by rw [Nat.dist_eq_sub_of_le (by omega)]; omega))
  simp only [datumT] at hh
  simp only [datumT,sampleValue_eq r hk,sampleValue_eq r (by omega : 1 ≤ k+n)]
  rcases hδ with rfl | rfl <;> simp only [one_mul,neg_one_mul] <;> linarith [hh.1,hh.2]

/-- Both star signs follow from the actual origin datum at the positive index. -/
theorem _root_.polyak.Growth.HRun.discounted_star_nonneg (r : HRun E A B β H) (t δ : ℝ)
    (hδ : δ=1 ∨ δ= -1) (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ starQuadratic δ (discountedPosition r.x t k) (discountedPosition r.σ t k)+
      δ*discountedValue (sampleValue r) t k := by
  rw [discounted_star_slack]
  apply mul_nonneg (Real.exp_pos _).le
  have hh := abs_le.mp (r.origin k hk)
  rw [sampleValue_eq r hk]
  rcases hδ with rfl | rfl <;> unfold starQuadratic <;> linarith [hh.1,hh.2]

/-- Every finite certificate slack is nonnegative on a table retaining its lags. -/
theorem _root_.polyak.Growth.HRun.certificateSlack_nonneg (r : HRun E A B β H)
    {m : C(Frequency, ℂ)} {t : ℝ} (cert : StrictCertificate m t)
    (hmem : ∀ n∈cert.lags,n ≤ H) (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ certificateSlack cert (discountedPosition r.x t) (discountedPosition r.σ t)
      (discountedValue (sampleValue r) t) k := by
  apply polyak.Energy.certificateSlack_nonneg
  · intro n hn
    simpa only [one_mul] using r.discounted_pair_nonneg t 1 (Or.inl rfl) k n hk (hmem n hn)
  · intro n hn
    simpa only [neg_one_mul,← sub_eq_add_neg] using
      r.discounted_pair_nonneg t (-1) (Or.inr rfl) k n hk (hmem n hn)
  · simpa only [one_mul] using r.discounted_star_nonneg t 1 (Or.inl rfl) k hk
  · simpa only [neg_one_mul,← sub_eq_add_neg] using
      r.discounted_star_nonneg t (-1) (Or.inr rfl) k hk

/-- Actual origin constraints bound every value used in the boundary sum. -/
theorem _root_.polyak.Growth.HRun.abs_discountedValue_le (r : HRun E A B β H) (t : ℝ) (k : ℕ) :
    |discountedValue (sampleValue r) t k| ≤ discountedEnergy r.x t k/2 := by
  by_cases hk : k=0
  · subst k
    simpa only [discountedValue,sampleValue,ite_true,mul_zero,abs_zero] using
      (div_nonneg (discountedEnergy_nonneg r.x t 0) (by norm_num : (0 : ℝ) ≤ 2))
  · have hk1 : 1 ≤ k := by omega
    have hh := abs_value_le_half_sq (r.origin k hk1)
    unfold discountedValue discountedEnergy
    rw [sampleValue_eq r hk1,abs_mul,abs_of_pos (Real.exp_pos _)]
    nlinarith [mul_le_mul_of_nonneg_left hh (Real.exp_pos (-2*k*t)).le]

/-- Article: the actual recurrence eliminates each discounted interior gradient.
Use: identify the precise translation-invariant kernel on every genuine run. -/
theorem _root_.polyak.Growth.HRun.filterEval_discountedGradient (r : HRun E A B β H) (t : ℝ) (hB : B ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) :
    filterEval (gradientFilter A B β t) (discountedInteger r.x t) k =
      discountedPosition r.σ t k := by
  have hrec := r.recurrence (k-1)
  rw [show k-1+2=k+1 by omega, show k-1+1=k by omega] at hrec
  have he : B • r.σ k = r.x (k+1)-A • r.x k+β • r.x (k-1) := by
    rw [hrec]
    module
  have hs : r.σ k =
      (1/B) • r.x (k+1)-(A/B) • r.x k+(β/B) • r.x (k-1) := by
    calc
      _ = (B⁻¹*B) • r.σ k := by simp [hB]
      _ = B⁻¹ • (B • r.σ k) := by rw [mul_smul]
      _ = _ := by rw [he]; simp only [smul_add, smul_sub, smul_smul]; module
  have hePos : Real.exp t*Real.exp (-((k+1 : ℕ)*t))=Real.exp (-(k*t)) := by
    simpa only [Nat.cast_one, one_mul] using exp_mul_discount t k 1
  have heNeg : Real.exp (-t)*Real.exp (-((k-1 : ℕ)*t))=Real.exp (-(k*t)) := by
    rw [← Real.exp_add]
    congr 1
    rw [Nat.cast_sub hk]
    push_cast
    ring
  rw [filterEval_gradient]
  have hkPos : ((k : ℤ)+1).toNat=k+1 := by omega
  have hkNeg : ((k : ℤ)-1).toNat=k-1 := by omega
  simp only [discountedInteger, Int.toNat_natCast, hkPos, hkNeg, discountedPosition]
  rw [hs]
  simp only [smul_add, smul_sub, smul_smul]
  have hcPos : Real.exp t/B*Real.exp (-((k+1 : ℕ)*t))=Real.exp (-(k*t))*(1/B) := by
    rw [div_eq_mul_inv, mul_right_comm, hePos]
    ring
  have hcNeg : β*Real.exp (-t)/B*Real.exp (-((k-1 : ℕ)*t))=Real.exp (-(k*t))*(β/B) := by
    calc
      _ = (β/B)*(Real.exp (-t)*Real.exp (-((k-1 : ℕ)*t))) := by ring
      _ = _ := by rw [heNeg]; ring
  rw [hcPos,hcNeg]
  module

/-- Article: identification of the actual full quadratic kernel with Q.
Use: all lagged gradients are eliminated using genuine recurrence identities. -/
theorem _root_.polyak.Growth.HRun.kernelEval_eq_certificateQuadratic (r : HRun E A B β H) {m : C(Frequency, ℂ)}
    {t : ℝ} (cert : StrictCertificate m t) (hB : B ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    kernelEval (certificateKernel A B β t cert) (discountedInteger r.x t) k =
      certificateQuadratic cert (discountedPosition r.x t)
        (discountedPosition r.σ t) k := by
  rw [kernelEval_certificate]
  have hgrad (n : ℕ) :
      filterEval (gradientFilter A B β t) (discountedInteger r.x t) ((k : ℤ)+n) =
        discountedPosition r.σ t (k+n) := by
    simpa only [Nat.cast_add] using r.filterEval_discountedGradient t hB (k+n) (by omega)
  simp only [r.filterEval_discountedGradient t hB k hk, hgrad, discountedInteger,
    Int.toNat_natCast, Int.toNat_add_nat (by omega : (0 : ℤ) ≤ k), certificateQuadratic]


/-- Article: Lemma energy. Use: the complete strict-certificate estimate for all actual functions
and finite dimensions; every symbol and interpolation hypothesis is discharged. -/
theorem _root_.polyak.Duality.StrictCertificate.horizonWindowEnergyBound {A B β t : ℝ} {H : ℕ}
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t) (hB : B ≠ 0)
    (hmem : ∀ n∈cert.lags,n ≤ H) :
    ∃ K : ℝ, ∃ w : ℕ, 0 < K ∧ FiniteHorizon.WindowEnergyBound A B β t K H w := by
  let kernel := certificateKernel A B β t cert
  obtain ⟨R,hR,hsupport⟩ := exists_kernel_radius kernel (cert.lags.sup id+2)
  let w := 2*R
  have hw : ∀ n ∈ cert.lags, n ≤ w := by
    intro n hn
    have hh : n ≤ cert.lags.sup id := Finset.le_sup (f := id) hn
    dsimp [w]
    omega
  have hwpos : 1 ≤ w := by dsimp [w]; omega
  let M := kernelSize kernel + valueBoundaryConstant cert
  have hM : 0 ≤ M := add_nonneg (kernelSize_nonneg _) (valueBoundaryConstant_nonneg _)
  let K := M/cert.ε+1
  have hK : 0 < K := by
    have hh := div_nonneg hM cert.ε_pos.le
    dsimp [K]
    linarith
  refine ⟨K,w,hK,fun d r i j hi hij => ?_⟩
  let f := discountedPosition r.x t
  let σ := discountedPosition r.σ t
  let h := discountedValue (sampleValue r) t
  let b := discountedEnergy r.x t
  have hb : ∀ k, 0 ≤ b k := discountedEnergy_nonneg r.x t
  have hf : (fun k => ‖f k‖^2)=b := funext (norm_discountedPosition_sq r.x t)
  have hquad := sum_kernelEval_nat_interval_le kernel f
    (certificateKernel_symbol_le A B β t hB cert) R hsupport i j hi hij
  have heq : (∑ k ∈ Finset.Icc i j, kernelEval kernel (fun l => f l.toNat) k) =
      ∑ k ∈ Finset.Icc i j, certificateQuadratic cert f σ k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact r.kernelEval_eq_certificateQuadratic cert hB k
      (by have := (Finset.mem_Icc.mp hk).1; omega)
  rw [heq, hf] at hquad
  have hvalues := abs_sum_certificateValue_le cert hb hij hw
    (fun l _ => r.abs_discountedValue_le t l)
  change |∑ k ∈ Finset.Icc i j, certificateValue cert h k| ≤
    valueBoundaryConstant cert*(window b w i+window b w j) at hvalues
  have hslacks : 0 ≤ ∑ k ∈ Finset.Icc i j, certificateSlack cert f σ h k :=
    Finset.sum_nonneg (fun k hk => r.certificateSlack_nonneg cert hmem k
      (by have := (Finset.mem_Icc.mp hk).1; omega))
  simp_rw [certificateSlack_eq] at hslacks
  rw [Finset.sum_add_distrib] at hslacks
  have hvalup := (le_abs_self (∑ k ∈ Finset.Icc i j, certificateValue cert h k)).trans hvalues
  have hnorm : cert.ε*(∑ k ∈ Finset.Icc i j, b k) ≤ M*(window b w i+window b w j) := by
    change (∑ k ∈ Finset.Icc i j, certificateQuadratic cert f σ k) ≤
      -cert.ε*(∑ k ∈ Finset.Icc i j,b k)+kernelSize kernel*(window b w i+window b w j) at hquad
    dsimp [M]
    linarith
  have hwin : 0 ≤ window b w i+window b w j := add_nonneg (window_nonneg hb _ _) (window_nonneg hb _ _)
  have hdiv : (∑ k ∈ Finset.Icc i j,b k) ≤ (M/cert.ε)*(window b w i+window b w j) := by
    calc
      _ ≤ (M*(window b w i+window b w j))/cert.ε :=
        (le_div_iff₀ cert.ε_pos).mpr (by nlinarith)
      _ = _ := by ring
  have hfinal : (∑ k ∈ Finset.Icc i j,b k) ≤ K*(window b w i+window b w j) := by
    dsimp [K]
    nlinarith
  simpa only [mass, Finset.Ico_add_one_right_eq_Icc, ← window_eq_energyWindow] using hfinal


end
end polyak.Growth.FiniteHorizon
