import polyak.General.IQC.CertificateSpace
import polyak.Interpolation.Extension

/-! Article: lem:iqc(a). The nonnegative whole-line IQC follows from
the actual normalized function, with its values cancelled exactly. -/
noncomputable section
namespace polyak.General.IQC
open polyak Energy Interpolation Duality Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : C(Frequency,ℂ)} {t : ℝ}

theorem zCertificate_nonneg_of_slacks (cert : StrictCertificate m t)
    {x σ : ℤ → E} {v : ℤ → ℝ}
    (hx : ZSquareSummable x) (hσ : ZSquareSummable σ) (hv : Summable v)
    (hp : ∀ k n, n∈cert.lags →
      0≤pairQuadratic 1 (x k) (Real.exp (n*t) • x (k+n))
        (σ k) (Real.exp (n*t) • σ (k+n))+(Real.exp (2*n*t)*v (k+n)-v k))
    (hn : ∀ k n, n∈cert.lags →
      0≤pairQuadratic (-1) (x k) (Real.exp (n*t) • x (k+n))
        (σ k) (Real.exp (n*t) • σ (k+n))-(Real.exp (2*n*t)*v (k+n)-v k))
    (hsp : ∀ k,0≤starQuadratic 1 (x k) (σ k)+v k)
    (hsm : ∀ k,0≤starQuadratic (-1) (x k) (σ k)-v k) :
    0≤∑' k,zCertificateQuadratic cert x σ k := by
  apply zCertificate_nonneg cert hx hσ hv
  intro k
  have hq : zCertificateQuadratic cert x σ k=
      certificateQuadratic cert (fun j : ℕ => x (k+j)) (fun j : ℕ => σ (k+j)) 0 := by
    simp only [zCertificateQuadratic,certificateQuadratic,Nat.zero_add,Int.natCast_zero,add_zero]
  have hv' : zCertificateValue cert v k=certificateValue cert (fun j : ℕ => v (k+j)) 0 := by
    rw [certificateValue_eq_differences]
    simp only [zCertificateValue,Nat.zero_add,Int.natCast_zero,add_zero]
  rw [hq,hv',← certificateSlack_eq]
  apply certificateSlack_nonneg
  · intro n hn'; simpa using hp k n hn'
  · intro n hn'; simpa using hn k n hn'
  · simpa using hsp k
  · simpa using hsm k

def zUnscale (t : ℝ) (x : ℤ → E) (k : ℤ) : E := Real.exp ((k:ℝ)*t) • x k
def zScaledGradient [CompleteSpace E] (ψ : E → ℝ) (t : ℝ) (x : ℤ → E) (k : ℤ) : E :=
  Real.exp (-((k:ℝ)*t)) • gradient ψ (zUnscale t x k)
def zScaledValue (ψ : E → ℝ) (t : ℝ) (x : ℤ → E) (k : ℤ) : ℝ :=
  Real.exp (-2*(k:ℝ)*t)*ψ (zUnscale t x k)

theorem exp_cancel_z (a : ℝ) : Real.exp (-a)*Real.exp a=1 := by
  rw [← Real.exp_add]; simp

theorem zScaledGradient_norm [CompleteSpace E] {ψ : E → ℝ} (hψ : NormalizedSmooth ψ)
    (t : ℝ) (x : ℤ → E) (k : ℤ) : ‖zScaledGradient ψ t x k‖≤‖x k‖ := by
  have h := hψ.grad_lipschitz.dist_le_mul (zUnscale t x k) 0
  simp only [hψ.gradient_zero,dist_zero_right,NNReal.coe_one,one_mul] at h
  rw [zScaledGradient,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq
  simp only [zUnscale,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← mul_assoc,exp_cancel_z,one_mul]

theorem zScaledValue_bound [CompleteSpace E] {ψ : E → ℝ} (hψ : NormalizedSmooth ψ)
    (t : ℝ) (x : ℤ → E) (k : ℤ) : |zScaledValue ψ t x k|≤(1/2:ℝ)*‖x k‖^2 := by
  have htab := hψ.tableFeasible (fun i : Option ℤ => i.elim 0 (zUnscale t x))
  have h := table_abs_value_le_half_sq htab none rfl hψ.gradient_zero hψ.value_zero (some k)
  change |ψ (zUnscale t x k)|≤(1/2:ℝ)*‖zUnscale t x k‖^2 at h
  rw [zScaledValue,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq
  simp only [zUnscale,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow]
  have he : Real.exp (-2*(k:ℝ)*t)*(Real.exp ((k:ℝ)*t))^2=1 := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    convert Real.exp_zero using 2
    push_cast
    ring
  nlinarith [he]

def zDiscount (t : ℝ) (u : ℤ → E) (k : ℤ) : E := Real.exp (-((k:ℝ)*t)) • u k
def zDiscountValue (t : ℝ) (v : ℤ → ℝ) (k : ℤ) : ℝ := Real.exp (-2*(k:ℝ)*t)*v k

theorem zDiscount_shift (t : ℝ) (u : ℤ → E) (k : ℤ) (n : ℕ) :
    Real.exp (n*t) • zDiscount t u (k+n)=Real.exp (-((k:ℝ)*t)) • u (k+n) := by
  dsimp [zDiscount]
  rw [smul_smul,← Real.exp_add]
  congr 2
  push_cast
  ring

theorem zDiscountValue_shift (t : ℝ) (v : ℤ → ℝ) (k : ℤ) (n : ℕ) :
    Real.exp (2*n*t)*zDiscountValue t v (k+n)-zDiscountValue t v k=
      Real.exp (-2*(k:ℝ)*t)*(v (k+n)-v k) := by
  dsimp [zDiscountValue]
  have he : Real.exp (2*n*t)*Real.exp (-2*((k+n:ℤ):ℝ)*t)=Real.exp (-2*(k:ℝ)*t) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [← mul_assoc,he,mul_sub]

theorem zDiscount_unscale (t : ℝ) (x : ℤ → E) : zDiscount t (zUnscale t x)=x := by
  funext k
  simp only [zDiscount,zUnscale,smul_smul,exp_cancel_z,one_smul]

theorem zDiscount_pair (t δ : ℝ) (x σ : ℤ → E) (k : ℤ) (n : ℕ) :
    pairQuadratic δ (zDiscount t x k) (Real.exp (n*t) • zDiscount t x (k+n))
      (zDiscount t σ k) (Real.exp (n*t) • zDiscount t σ (k+n))=
      Real.exp (-2*(k:ℝ)*t)*pairQuadratic δ (x k) (x (k+n)) (σ k) (σ (k+n)) := by
  rw [zDiscount_shift,zDiscount_shift]
  change pairQuadratic δ (Real.exp (-((k:ℝ)*t)) • x k) _
    (Real.exp (-((k:ℝ)*t)) • σ k) _= _
  rw [pairQuadratic_smul]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem zDiscount_star (t δ : ℝ) (x σ : ℤ → E) (k : ℤ) :
    starQuadratic δ (zDiscount t x k) (zDiscount t σ k)=
      Real.exp (-2*(k:ℝ)*t)*starQuadratic δ (x k) (σ k) := by
  rw [zDiscount,zDiscount,starQuadratic_smul]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem discounted_table_IQC (cert : StrictCertificate m t)
    {x σ : ℤ → E} {v : ℤ → ℝ}
    (htable : TableFeasible (fun i : Option ℤ => i.elim 0 x)
      (fun i : Option ℤ => i.elim 0 σ) (fun i : Option ℤ => i.elim 0 v))
    (hx : ZSquareSummable (zDiscount t x)) (hσ : ZSquareSummable (zDiscount t σ))
    (hv : Summable (zDiscountValue t v)) :
    0≤∑' k,zCertificateQuadratic cert (zDiscount t x) (zDiscount t σ) k := by
  apply zCertificate_nonneg_of_slacks cert hx hσ hv
  · intro k n _
    rw [zDiscount_pair,zDiscountValue_shift,← mul_add]
    apply mul_nonneg (Real.exp_pos _).le
    have ht := (abs_le.mp (htable (some k) (some (k+n)))).1
    have he := pair_slack_eq (fun i : Option ℤ => i.elim 0 x)
      (fun i : Option ℤ => i.elim 0 σ) (fun i : Option ℤ => i.elim 0 v) (some k) (some (k+n)) 1
    simp only [Option.elim_some,one_mul] at he
    linarith
  · intro k n _
    rw [zDiscount_pair,zDiscountValue_shift,← mul_sub]
    apply mul_nonneg (Real.exp_pos _).le
    have ht := (abs_le.mp (htable (some k) (some (k+n)))).2
    have he := pair_slack_eq (fun i : Option ℤ => i.elim 0 x)
      (fun i : Option ℤ => i.elim 0 σ) (fun i : Option ℤ => i.elim 0 v) (some k) (some (k+n)) (-1)
    simp only [Option.elim_some,neg_one_mul] at he
    linarith
  · intro k
    rw [zDiscount_star,zDiscountValue,← mul_add]
    apply mul_nonneg (Real.exp_pos _).le
    have ht := (abs_le.mp (htable none (some k))).1
    have he := star_slack_eq (fun i : Option ℤ => i.elim 0 x)
      (fun i : Option ℤ => i.elim 0 σ) (fun i : Option ℤ => i.elim 0 v) none (some k) rfl rfl rfl 1
    simp only [Option.elim_some,one_mul] at he
    linarith
  · intro k
    rw [zDiscount_star,zDiscountValue,← mul_sub]
    apply mul_nonneg (Real.exp_pos _).le
    have ht := (abs_le.mp (htable none (some k))).2
    have he := star_slack_eq (fun i : Option ℤ => i.elim 0 x)
      (fun i : Option ℤ => i.elim 0 σ) (fun i : Option ℤ => i.elim 0 v) none (some k) rfl rfl rfl (-1)
    simp only [Option.elim_some,neg_one_mul] at he
    linarith

theorem normalizedSmooth_IQC [CompleteSpace E] (cert : StrictCertificate m t)
    {ψ : E → ℝ} (hψ : NormalizedSmooth ψ) {x : ℤ → E} (hx : ZSquareSummable x) :
    0≤∑' k,zCertificateQuadratic cert x (zScaledGradient ψ t x) k := by
  have hσ : ZSquareSummable (zScaledGradient ψ t x) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hx
    intro k
    exact pow_le_pow_left₀ (norm_nonneg _) (zScaledGradient_norm hψ t x k) 2
  have hv : Summable (zScaledValue ψ t x) := by
    apply (Summable.mul_left (1/2:ℝ) hx).of_norm_bounded
    intro k
    simpa only [Real.norm_eq_abs] using zScaledValue_bound hψ t x k
  have ht := hψ.tableFeasible (fun i : Option ℤ => i.elim 0 (zUnscale t x))
  have ht' : TableFeasible (fun i : Option ℤ => i.elim 0 (zUnscale t x))
      (fun i : Option ℤ => i.elim 0 (fun k => gradient ψ (zUnscale t x k)))
      (fun i : Option ℤ => i.elim 0 (fun k => ψ (zUnscale t x k))) := by
    convert ht using 1 <;> funext i <;> cases i <;> simp [hψ.gradient_zero,hψ.value_zero]
  have hh := discounted_table_IQC cert ht' (by simpa only [zDiscount_unscale] using hx) hσ hv
  rw [zDiscount_unscale] at hh
  exact hh

def sourceGradientL2 [CompleteSpace E] {ψ : E → ℝ} (hψ : NormalizedSmooth ψ)
    (t : ℝ) (x : ZSpace E) : ZSpace E := toZL2 (zScaledGradient ψ t x) (by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (zlp_squareSummable x)
  intro k
  exact pow_le_pow_left₀ (norm_nonneg _) (zScaledGradient_norm hψ t x k) 2)
@[simp] theorem sourceGradientL2_apply [CompleteSpace E] {ψ : E → ℝ} (hψ : NormalizedSmooth ψ)
    (t : ℝ) (x : ZSpace E) (k : ℤ) :
    sourceGradientL2 hψ t x k=zScaledGradient ψ t x k := rfl

end polyak.General.IQC
