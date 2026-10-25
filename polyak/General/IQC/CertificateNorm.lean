import polyak.General.IQC.CertificateBilinear

/-! Article: lem:iqc and lem:homotopy. Operator bounds depend only on
the finite certificate and exponent, uniformly over Hilbert spaces. -/
noncomputable section
namespace polyak.General.IQC
open polyak Energy Duality Spectral

section Bilinear
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
theorem innerB_norm_le (U V : K →L[ℝ] H) : ‖innerB U V‖≤‖U‖*‖V‖ := by
  apply (innerB U V).opNorm_le_bound₂ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro u v
  rw [innerB_apply,Real.norm_eq_abs]
  calc
    _≤‖U u‖*‖V v‖ := abs_real_inner_le_norm _ _
    _≤(‖U‖*‖u‖)*(‖V‖*‖v‖) := mul_le_mul (U.le_opNorm _) (V.le_opNorm _) (norm_nonneg _) (by positivity)
    _=‖U‖*‖V‖*‖u‖*‖v‖ := by ring

theorem pairB_norm_bound (δ e : ℝ) (X Y S T : K →L[ℝ] H) (he : 0≤e)
    (hδ : |δ|≤1) (hX : ‖X‖≤1) (hY : ‖Y‖≤e) (hS : ‖S‖≤1) (hT : ‖T‖≤e) :
    ‖pairB δ X Y S T‖≤(1+e)^2 := by
  have hYX : ‖Y-X‖≤1+e := (norm_sub_le _ _).trans (by linarith)
  have hTS : ‖T-S‖≤1+e := (norm_sub_le _ _).trans (by linarith)
  have hST : ‖S+T‖≤1+e := (norm_add_le _ _).trans (by linarith)
  have hA : ‖innerB (Y-X) (Y-X)‖≤(1+e)^2 := by
    apply (innerB_norm_le _ _).trans
    nlinarith [norm_nonneg (Y-X)]
  have hB : ‖innerB (T-S) (T-S)‖≤(1+e)^2 := by
    apply (innerB_norm_le _ _).trans
    nlinarith [norm_nonneg (T-S)]
  have hC : ‖innerB (S+T) (Y-X)‖≤(1+e)^2 := by
    apply (innerB_norm_le _ _).trans
    nlinarith [mul_nonneg (sub_nonneg.2 hST) (sub_nonneg.2 hYX),norm_nonneg (S+T),norm_nonneg (Y-X)]
  calc
    ‖pairB δ X Y S T‖≤‖(1/4:ℝ) • (innerB (Y-X) (Y-X)-innerB (T-S) (T-S))‖+
        ‖(δ/2) • innerB (S+T) (Y-X)‖ := by simpa only [pairB] using norm_sub_le ((1/4:ℝ) • (innerB (Y-X) (Y-X)-innerB (T-S) (T-S))) ((δ/2) • innerB (S+T) (Y-X))
    _≤(1/4:ℝ)*(‖innerB (Y-X) (Y-X)‖+‖innerB (T-S) (T-S)‖)+
        (|δ|/2)*‖innerB (S+T) (Y-X)‖ := by
      have hD := ContinuousLinearMap.opNorm_smul_le (1/4:ℝ) (innerB (Y-X) (Y-X)-innerB (T-S) (T-S))
      have hE := ContinuousLinearMap.opNorm_smul_le (δ/2) (innerB (S+T) (Y-X))
      norm_num only [Real.norm_eq_abs,abs_div,abs_one,abs_of_pos (by norm_num : 0<(4:ℝ)),
        abs_of_pos (by norm_num : 0<(2:ℝ))] at hD hE
      exact add_le_add (hD.trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num))) hE
    _≤(1+e)^2 := by nlinarith [norm_nonneg (innerB (S+T) (Y-X)),sq_nonneg (1+e)]

theorem starB_norm_bound (δ : ℝ) (X S : K →L[ℝ] H) (hδ : |δ|≤1)
    (hX : ‖X‖≤1) (hS : ‖S‖≤1) : ‖starB δ X S‖≤1 := by
  have hXX := innerB_norm_le X X
  have hSS := innerB_norm_le S S
  have hSX := innerB_norm_le S X
  have hX2 : ‖X‖*‖X‖≤1 := by nlinarith [norm_nonneg X]
  have hS2 : ‖S‖*‖S‖≤1 := by nlinarith [norm_nonneg S]
  have hSX' : ‖S‖*‖X‖≤1 := by nlinarith [mul_nonneg (sub_nonneg.2 hS) (sub_nonneg.2 hX)]
  calc
    ‖starB δ X S‖≤‖(1/4:ℝ) • (innerB X X-innerB S S)‖+
      ‖(δ/2) • innerB S X‖ := by simpa only [starB] using norm_sub_le ((1/4:ℝ) • (innerB X X-innerB S S)) ((δ/2) • innerB S X)
    _≤(1/4:ℝ)*(‖innerB X X‖+‖innerB S S‖)+(|δ|/2)*‖innerB S X‖ := by
      have hD := ContinuousLinearMap.opNorm_smul_le (1/4:ℝ) (innerB X X-innerB S S)
      have hE := ContinuousLinearMap.opNorm_smul_le (δ/2) (innerB S X)
      norm_num only [Real.norm_eq_abs,abs_div,abs_one,abs_of_pos (by norm_num : 0<(4:ℝ)),
        abs_of_pos (by norm_num : 0<(2:ℝ))] at hD hE
      exact add_le_add (hD.trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num))) hE
    _≤1 := by nlinarith [norm_nonneg (innerB S X)]
end Bilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : C(Frequency,ℂ)} {t : ℝ}

local instance : NormedSpace ℝ ((ZSpace E × ZSpace E) →L[ℝ] ℝ) := inferInstance
local instance : SeminormedAddCommGroup ((ZSpace E × ZSpace E) →L[ℝ] ℝ) := inferInstance

theorem zFirst_norm_le : ‖zFirst (E:=E)‖≤1 := by
  apply (zFirst (E:=E)).opNorm_le_bound (by norm_num)
  intro u
  change ‖u.1‖≤1*‖u‖
  simpa only [one_mul] using norm_fst_le u
theorem zSecond_norm_le : ‖zSecond (E:=E)‖≤1 := by
  apply (zSecond (E:=E)).opNorm_le_bound (by norm_num)
  intro u
  change ‖u.2‖≤1*‖u‖
  simpa only [one_mul] using norm_snd_le u

theorem zLagFirst_norm_le (t : ℝ) (n : ℕ) : ‖zLagFirst (E:=E) t n‖≤Real.exp (n*t) := by
  apply (zLagFirst (E:=E) t n).opNorm_le_bound (Real.exp_pos _).le
  intro u
  change ‖Real.exp (n*t) • zShift n u.1‖≤Real.exp (n*t)*‖u‖
  apply (norm_smul_le _ _).trans
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),zShift_norm]
  exact mul_le_mul_of_nonneg_left (norm_fst_le u) (Real.exp_pos _).le

theorem zLagSecond_norm_le (t : ℝ) (n : ℕ) : ‖zLagSecond (E:=E) t n‖≤Real.exp (n*t) := by
  apply (zLagSecond (E:=E) t n).opNorm_le_bound (Real.exp_pos _).le
  intro u
  change ‖Real.exp (n*t) • zShift n u.2‖≤Real.exp (n*t)*‖u‖
  apply (norm_smul_le _ _).trans
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),zShift_norm]
  exact mul_le_mul_of_nonneg_left (norm_snd_le u) (Real.exp_pos _).le

def certificateNormBound (cert : StrictCertificate m t) : ℝ :=
  (∑ n ∈ cert.lags,|2*Real.exp (-(n*t))| *(|cert.α n|+|cert.β n|)*(1+Real.exp (n*t))^2)+
    4*|cert.γplus|+4*|cert.γminus|
theorem certificateNormBound_nonneg (cert : StrictCertificate m t) : 0≤certificateNormBound cert := by
  unfold certificateNormBound
  positivity

theorem lagForm_norm_le (t : ℝ) (n : ℕ) {δ : ℝ} (hδ : |δ|≤1) :
    ‖lagForm (E:=E) t n δ‖≤(1+Real.exp (n*t))^2 :=
  pairB_norm_bound δ _ _ _ _ _ (Real.exp_pos _).le hδ zFirst_norm_le
    (zLagFirst_norm_le t n) zSecond_norm_le (zLagSecond_norm_le t n)
theorem minimizerForm_norm_le {δ : ℝ} (hδ : |δ|≤1) : ‖minimizerForm (E:=E) δ‖≤1 :=
  starB_norm_bound δ _ _ hδ zFirst_norm_le zSecond_norm_le

theorem rawCertificateForm_norm_le (cert : StrictCertificate m t) :
    ‖rawCertificateForm (E:=E) cert‖≤certificateNormBound cert := by
  have hlag (n : ℕ) : ‖(2*Real.exp (-(n*t))) •
      ((cert.α n) • lagForm (E:=E) t n 1+(cert.β n) • lagForm (E:=E) t n (-1))‖≤
      |2*Real.exp (-(n*t))| *(|cert.α n|+|cert.β n|)*(1+Real.exp (n*t))^2 := by
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_eq_abs]
    calc
      _≤|2*Real.exp (-(n*t))| *(‖(cert.α n) • lagForm (E:=E) t n 1‖+
          ‖(cert.β n) • lagForm (E:=E) t n (-1)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _)
      _≤|2*Real.exp (-(n*t))| *(|cert.α n| *(1+Real.exp (n*t))^2+
          |cert.β n| *(1+Real.exp (n*t))^2) := by
        gcongr
        · exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
            (by rw [Real.norm_eq_abs]; gcongr; exact lagForm_norm_le t n (by norm_num))
        · exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
            (by rw [Real.norm_eq_abs]; gcongr; exact lagForm_norm_le t n (by norm_num))
      _=_ := by ring
  have hstar (δ γ : ℝ) (hδ : |δ|≤1) : ‖(4*γ) • minimizerForm (E:=E) δ‖≤4*|γ| := by
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : 0<(4:ℝ))]
    have := minimizerForm_norm_le (E:=E) hδ
    nlinarith [abs_nonneg γ]
  unfold rawCertificateForm certificateNormBound
  let W : ℕ → BilinearIQC (ZSpace E) := fun n =>
    (2*Real.exp (-(n*t))) • (cert.α n • lagForm t n 1+cert.β n • lagForm t n (-1))
  have hsum : ‖∑ n ∈ cert.lags,W n‖≤
      ∑ n ∈ cert.lags,|2*Real.exp (-(n*t))| * (|cert.α n|+|cert.β n|)*(1+Real.exp (n*t))^2 :=
    (norm_sum_le cert.lags W).trans (Finset.sum_le_sum (fun n _ => hlag n))
  have h1 := norm_add_le (∑ n ∈ cert.lags,W n) ((4*cert.γplus) • minimizerForm (E:=E) 1)
  have h2 := norm_add_le ((∑ n ∈ cert.lags,W n)+(4*cert.γplus) • minimizerForm (E:=E) 1)
    ((4*cert.γminus) • minimizerForm (E:=E) (-1))
  exact h2.trans (add_le_add (h1.trans (add_le_add hsum (hstar 1 _ (by norm_num))))
    (hstar (-1) _ (by norm_num)))

theorem certificateForm_norm_le (cert : StrictCertificate m t) :
    ‖certificateForm (E:=E) cert‖≤certificateNormBound cert := by
  unfold certificateForm
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  norm_num only [Real.norm_eq_abs,abs_div,abs_one,abs_of_pos (by norm_num : 0<(2:ℝ))]
  have hnorm := norm_add_le (rawCertificateForm (E:=E) cert) (rawCertificateForm (E:=E) cert).flip
  rw [ContinuousLinearMap.opNorm_flip] at hnorm
  nlinarith [rawCertificateForm_norm_le (E:=E) cert]

end polyak.General.IQC
