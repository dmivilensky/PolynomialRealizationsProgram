import polyak.General.IQC.CertificateSpace

/-! Article: lem:iqc. A genuine bounded real Hermitian two-channel form.
Its diagonal is precisely the absolutely convergent source quadratic sum. -/
noncomputable section
namespace polyak.General.IQC
open polyak Energy Duality Spectral

section Bilinear
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
def innerB (U V : K →L[ℝ] H) : K →L[ℝ] K →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp U V
@[simp] theorem innerB_apply (U V : K →L[ℝ] H) (u v : K) :
    innerB U V u v=inner ℝ (U u) (V v) := rfl

def pairB (δ : ℝ) (X Y S T : K →L[ℝ] H) : K →L[ℝ] K →L[ℝ] ℝ :=
  (1/4:ℝ) • (innerB (Y-X) (Y-X)-innerB (T-S) (T-S))-
    (δ/2) • innerB (S+T) (Y-X)
def starB (δ : ℝ) (X S : K →L[ℝ] H) : K →L[ℝ] K →L[ℝ] ℝ :=
  (1/4:ℝ) • (innerB X X-innerB S S)-(δ/2) • innerB S X

theorem pairB_diagonal (δ : ℝ) (X Y S T : K →L[ℝ] H) (u : K) :
    pairB δ X Y S T u u=pairQuadratic δ (X u) (Y u) (S u) (T u) := by
  simp only [pairB,sub_apply,add_apply,
    smul_apply,smul_eq_mul,innerB_apply,real_inner_self_eq_norm_sq,pairQuadratic]
theorem starB_diagonal (δ : ℝ) (X S : K →L[ℝ] H) (u : K) :
    starB δ X S u u=starQuadratic δ (X u) (S u) := by
  simp only [starB,sub_apply,smul_apply,
    smul_eq_mul,innerB_apply,real_inner_self_eq_norm_sq,starQuadratic]
end Bilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : C(Frequency,ℂ)} {t : ℝ}

def zFirst : ZSpace E×ZSpace E →L[ℝ] ZSpace E := ContinuousLinearMap.fst ℝ _ _
def zSecond : ZSpace E×ZSpace E →L[ℝ] ZSpace E := ContinuousLinearMap.snd ℝ _ _
def zLagFirst (t : ℝ) (n : ℕ) : ZSpace E×ZSpace E →L[ℝ] ZSpace E :=
  Real.exp (n*t) • (zShiftCLM n).comp zFirst
def zLagSecond (t : ℝ) (n : ℕ) : ZSpace E×ZSpace E →L[ℝ] ZSpace E :=
  Real.exp (n*t) • (zShiftCLM n).comp zSecond

def lagForm (t : ℝ) (n : ℕ) (δ : ℝ) : BilinearIQC (ZSpace E) :=
  pairB δ (zFirst (E:=E)) (zLagFirst t n) zSecond (zLagSecond t n)
def minimizerForm (δ : ℝ) : BilinearIQC (ZSpace E) :=
  starB δ (zFirst (E:=E)) zSecond

def rawCertificateForm (cert : StrictCertificate m t) : BilinearIQC (ZSpace E) :=
  (∑ n ∈ cert.lags, (2*Real.exp (-(n*t))) •
    ((cert.α n) • lagForm t n 1+
     (cert.β n) • lagForm t n (-1)))+
    (4*cert.γplus) • minimizerForm 1+
    (4*cert.γminus) • minimizerForm (-1)

def certificateForm (cert : StrictCertificate m t) : BilinearIQC (ZSpace E) :=
  (1/2:ℝ) • (rawCertificateForm cert+(rawCertificateForm (E:=E) cert).flip)

theorem certificateForm_symmetric (cert : StrictCertificate m t) (u v : ZSpace E×ZSpace E) :
    certificateForm cert u v=certificateForm cert v u := by
  simp only [certificateForm,add_apply,smul_apply,
    ContinuousLinearMap.flip_apply,smul_eq_mul]
  ring

theorem certificateForm_diagonal (cert : StrictCertificate m t) (u : ZSpace E×ZSpace E) :
    certificateForm cert u u=rawCertificateForm cert u u := by
  simp only [certificateForm,add_apply,smul_apply,
    ContinuousLinearMap.flip_apply,smul_eq_mul]
  ring

theorem certificateForm_diagonal_formula (cert : StrictCertificate m t) (x σ : ZSpace E) :
    certificateForm cert (x,σ) (x,σ)=
      (∑ n ∈ cert.lags,2*Real.exp (-(n*t))*
        (cert.α n*pairQuadratic 1 x (Real.exp (n*t) • zShift n x)
          σ (Real.exp (n*t) • zShift n σ)+
         cert.β n*pairQuadratic (-1) x (Real.exp (n*t) • zShift n x)
          σ (Real.exp (n*t) • zShift n σ)))+
        4*cert.γplus*starQuadratic 1 x σ+4*cert.γminus*starQuadratic (-1) x σ := by
  rw [certificateForm_diagonal]
  simp only [rawCertificateForm,sum_apply,add_apply,smul_apply,lagForm,minimizerForm,
    pairB_diagonal,starB_diagonal,zFirst,zSecond,smul_eq_mul]
  rfl

theorem pairQuadratic_tsum (δ : ℝ) (x y σ τ : ZSpace E) :
    pairQuadratic δ x y σ τ=∑' k,pairQuadratic δ (x k) (y k) (σ k) (τ k) := by
  have hx := zlp_squareSummable x
  have hy := zlp_squareSummable y
  have hσ := zlp_squareSummable σ
  have hτ := zlp_squareSummable τ
  unfold pairQuadratic
  rw [((Summable.sub (hy.sub hx) (hτ.sub hσ)).mul_left _).tsum_sub
    ((summable_Zinner (hσ.add hτ) (hy.sub hx)).mul_left _),tsum_mul_left,tsum_mul_left,
    (hy.sub hx).tsum_sub (hτ.sub hσ)]
  have hxy : ‖y-x‖^2=∑' k,‖y k-x k‖^2 := zlp_norm_sq (y-x)
  have hστ : ‖τ-σ‖^2=∑' k,‖τ k-σ k‖^2 := zlp_norm_sq (τ-σ)
  have hi : inner ℝ (σ+τ) (y-x)=∑' k,inner ℝ (σ k+τ k) (y k-x k) := lp.inner_eq_tsum (σ+τ) (y-x)
  rw [← hxy,← hστ,← hi]

theorem starQuadratic_tsum (δ : ℝ) (x σ : ZSpace E) :
    starQuadratic δ x σ=∑' k,starQuadratic δ (x k) (σ k) := by
  have hx := zlp_squareSummable x
  have hσ := zlp_squareSummable σ
  unfold starQuadratic
  rw [((Summable.sub hx hσ).mul_left _).tsum_sub
    ((summable_Zinner hσ hx).mul_left _),tsum_mul_left,tsum_mul_left,
    hx.tsum_sub hσ,← zlp_norm_sq,← zlp_norm_sq,← lp.inner_eq_tsum σ x]

theorem certificateForm_eq_tsum (cert : StrictCertificate m t) (x σ : ZSpace E) :
    certificateForm cert (x,σ) (x,σ)=∑' k,zCertificateQuadratic cert x σ k := by
  let lag (n : ℕ) (k : ℤ) := 2*Real.exp (-(n*t))*
    (cert.α n*pairQuadratic 1 (x k) (Real.exp (n*t) • x (k+n))
      (σ k) (Real.exp (n*t) • σ (k+n))+
     cert.β n*pairQuadratic (-1) (x k) (Real.exp (n*t) • x (k+n))
      (σ k) (Real.exp (n*t) • σ (k+n)))
  have hx := zlp_squareSummable x
  have hσ := zlp_squareSummable σ
  have hl (n : ℕ) : Summable (lag n) :=
    (((summable_Zpair hx ((hx.shift n).smul _) hσ ((hσ.shift n).smul _) 1).mul_left _).add
      ((summable_Zpair hx ((hx.shift n).smul _) hσ ((hσ.shift n).smul _) (-1)).mul_left _)).mul_left _
  have hsum : Summable (fun k => ∑ n ∈ cert.lags,lag n k) := summable_sum (fun n _ => hl n)
  have hp := (summable_Zstar hx hσ 1).mul_left (4*cert.γplus)
  have hn := (summable_Zstar hx hσ (-1)).mul_left (4*cert.γminus)
  change certificateForm cert (x,σ) (x,σ)=
    ∑' k,(((∑ n ∈ cert.lags,lag n k)+4*cert.γplus*starQuadratic 1 (x k) (σ k))+
      4*cert.γminus*starQuadratic (-1) (x k) (σ k))
  rw [(hsum.add hp).tsum_add hn,hsum.tsum_add hp,
    Summable.tsum_finsetSum (fun n _ => hl n),tsum_mul_left,tsum_mul_left,
    ← starQuadratic_tsum,← starQuadratic_tsum,certificateForm_diagonal]
  simp only [rawCertificateForm,sum_apply,add_apply,smul_apply,lagForm,minimizerForm,
    pairB_diagonal,starB_diagonal,zFirst,zSecond,smul_eq_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro n _
  dsimp [lag]
  rw [tsum_mul_left,
    ((summable_Zpair hx ((hx.shift n).smul _) hσ ((hσ.shift n).smul _) 1).mul_left _).tsum_add
      ((summable_Zpair hx ((hx.shift n).smul _) hσ ((hσ.shift n).smul _) (-1)).mul_left _),
    tsum_mul_left,tsum_mul_left]
  change _=2*Real.exp (-(n*t))*(cert.α n*
    (∑' k,pairQuadratic 1 (x k) ((Real.exp (n*t) • zShift n x) k)
      (σ k) ((Real.exp (n*t) • zShift n σ) k))+
    cert.β n*(∑' k,pairQuadratic (-1) (x k) ((Real.exp (n*t) • zShift n x) k)
      (σ k) ((Real.exp (n*t) • zShift n σ) k)))
  rw [← pairQuadratic_tsum,← pairQuadratic_tsum]
  rfl

end polyak.General.IQC
