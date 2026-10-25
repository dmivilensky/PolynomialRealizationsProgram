import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-! Article: Appendix D, the a priori half of Lemma homotopy.
The bounded Hermitian IQC is used as a bounded real bilinear form on the
two-channel Hilbert space. Its strict graph gap gives a uniform norm bound.
Neither invertibility nor stability of the nonlinear loop is assumed. -/
noncomputable section
namespace polyak.General.IQC

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

abbrev BilinearIQC (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  (H×H) →L[ℝ] (H×H) →L[ℝ] ℝ

def iqcValue (B : BilinearIQC H) (x y : H) : ℝ := B (x,y) (x,y)

theorem bounded_bilinear_abs (B : BilinearIQC H) (u v : H×H) :
    |B u v|≤‖B‖*‖u‖*‖v‖ := by
  calc
    _=‖B u v‖:=(Real.norm_eq_abs _).symm
    _≤‖B u‖*‖v‖:=(B u).le_opNorm v
    _≤(‖B‖*‖u‖)*‖v‖:=mul_le_mul_of_nonneg_right (B.le_opNorm u) (norm_nonneg v)

theorem quadratic_gap_bound {z f a b ε : ℝ}
    (_hz : 0≤z) (hf : 0≤f) (ha : 0≤a) (hb : 0≤b) (hε : 0<ε)
    (h : ε*z^2≤a*f*z+b*f^2) : z≤(1+(a+b)/ε)*f := by
  let D:=1+(a+b)/ε
  have hD : 1≤D:=by
    have hh : 0≤(a+b)/ε:=div_nonneg (add_nonneg ha hb) hε.le
    dsimp [D]
    linarith
  have he : ε*D=a+b+ε:=by dsimp [D]; field_simp; ring
  by_cases hf0 : f=0
  · subst f
    simp only [mul_zero,zero_mul,zero_pow (by omega : 2≠0),add_zero] at h ⊢
    have hh : z^2≤0:=by
      apply (mul_le_mul_iff_right₀ hε).mp
      simpa only [mul_comm,zero_mul,mul_zero] using h
    nlinarith
  have hfp : 0<f:=lt_of_le_of_ne hf (Ne.symm hf0)
  by_contra hn
  have hDz : D*f<z:=lt_of_not_ge hn
  have hfz : f<z:=by nlinarith
  have hzp : 0<z:=hfp.trans hfz
  have h1:=mul_lt_mul_of_pos_right hDz (mul_pos hε hzp)
  have h2:=mul_lt_mul_of_pos_right (by linarith [he] : a+b<ε*D) (mul_pos hfp hzp)
  have h3:=mul_nonneg hb (show 0≤f*z-f^2 by nlinarith)
  nlinarith

theorem iqc_perturbation_bound (B : BilinearIQC H) (G : H →L[ℝ] H) (z f : H) :
    iqcValue B (G z+f) z≤ iqcValue B (G z) z+
      (2*‖B‖*max ‖G‖ 1)*‖f‖*‖z‖+‖B‖*‖f‖^2 := by
  let p : H×H:=(G z,z)
  let d : H×H:=(f,0)
  have hp : ‖p‖≤max ‖G‖ 1*‖z‖:=by
    change max ‖G z‖ ‖z‖≤_
    apply max_le
    · exact (G.le_opNorm z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg z))
    · have hh:=mul_le_mul_of_nonneg_right (le_max_right ‖G‖ 1) (norm_nonneg z)
      simpa only [one_mul] using hh
  have hd : ‖d‖=‖f‖:=by simp [d,Prod.norm_def]
  have he : iqcValue B (G z+f) z=
      iqcValue B (G z) z+B p d+B d p+B d d:=by
    have hp : (G z+f,z)=p+d:=by simp [p,d]
    rw [iqcValue,hp]
    change B (p+d) (p+d)=B p p+B p d+B d p+B d d
    simp only [map_add,add_apply]
    ring
  have hpd : B p d≤‖B‖*(max ‖G‖ 1*‖z‖)*‖f‖:=by
    calc
      _≤|B p d|:=le_abs_self _
      _≤‖B‖*‖p‖*‖d‖:=bounded_bilinear_abs B p d
      _≤_:=by rw [hd]; gcongr
  have hdp : B d p≤‖B‖*‖f‖*(max ‖G‖ 1*‖z‖):=by
    calc
      _≤|B d p|:=le_abs_self _
      _≤‖B‖*‖d‖*‖p‖:=bounded_bilinear_abs B d p
      _≤_:=by rw [hd]; gcongr
  have hdd : B d d≤‖B‖*‖f‖^2:=by
    calc
      _≤|B d d|:=le_abs_self _
      _≤‖B‖*‖d‖*‖d‖:=bounded_bilinear_abs B d d
      _=_:=by rw [hd]; ring
  rw [he]
  nlinarith

/-- The explicit constant depends on coefficient bounds, not on the Hilbert
space, its dimension, the nonlinear potential or the homotopy parameter. -/
def aprioriConstant (M g ε : ℝ) : ℝ := g*(1+(2*M*max g 1+M)/ε)+1

theorem aprioriConstant_pos {M g ε : ℝ} (hM : 0≤M) (hg : 0≤g) (hε : 0<ε) :
    0<aprioriConstant M g ε := by unfold aprioriConstant; positivity

theorem uniform_apriori_bound (B : BilinearIQC H) (G : H →L[ℝ] H)
    {M g : ℝ} (hM : ‖B‖≤M) (hG : ‖G‖≤g)
    {ε : ℝ} (hε : 0<ε)
    (hneg : ∀ z : H,iqcValue B (G z) z≤ -ε*‖z‖^2)
    (x z f : H) (he : x=G z+f) (hpos : 0≤ iqcValue B x z) :
    ‖x‖≤aprioriConstant M g ε*‖f‖ := by
  have hMp : 0≤M:=(norm_nonneg B).trans hM
  have hgp : 0≤g:=(norm_nonneg G).trans hG
  let a:=2*M*max g 1
  let b:=M
  let D:=1+(a+b)/ε
  have ha : 0≤a:=by dsimp [a]; positivity
  have hb : 0≤b:=hMp
  have hpert : iqcValue B (G z+f) z≤ iqcValue B (G z) z+a*‖f‖*‖z‖+b*‖f‖^2:=by
    apply (iqc_perturbation_bound B G z f).trans
    dsimp [a,b]
    gcongr
  have hg:=hneg z
  rw [he] at hpos ⊢
  have hq : ε*‖z‖^2≤a*‖f‖*‖z‖+b*‖f‖^2:=by
    dsimp [a,b]
    linarith
  have hz : ‖z‖≤D*‖f‖:=quadratic_gap_bound (norm_nonneg _) (norm_nonneg _) ha hb hε hq
  calc
    ‖G z+f‖≤‖G z‖+‖f‖:=norm_add_le _ _
    _≤g*‖z‖+‖f‖:=by
      have hh:=(G.le_opNorm z).trans (mul_le_mul_of_nonneg_right hG (norm_nonneg z))
      linarith
    _≤g*(D*‖f‖)+‖f‖:=by
      have hh:=mul_le_mul_of_nonneg_left hz hgp
      linarith
    _=aprioriConstant M g ε*‖f‖:=by unfold aprioriConstant; dsimp [D,a,b]; ring

/-- The abstract bounded-Hermitian-IQC a priori estimate. -/
theorem exists_uniform_apriori (B : BilinearIQC H) (G : H →L[ℝ] H)
    {ε : ℝ} (hε : 0<ε)
    (hneg : ∀ z : H,iqcValue B (G z) z≤ -ε*‖z‖^2) :
    ∃ C : ℝ,0<C ∧ ∀ x z f : H,x=G z+f → 0≤ iqcValue B x z → ‖x‖≤C*‖f‖ :=
  ⟨aprioriConstant ‖B‖ ‖G‖ ε,
    aprioriConstant_pos (norm_nonneg B) (norm_nonneg G) hε,
    fun x z f he hpos => uniform_apriori_bound B G le_rfl le_rfl hε hneg x z f he hpos⟩

end polyak.General.IQC
