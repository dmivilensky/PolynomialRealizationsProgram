import polyak.Waves.Complex
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
Article: Appendix A, strict minimizer slack for every finite optimal spectrum.
Use: a nonzero finite trigonometric sum of positive frequencies cannot have
an exponentially vanishing negative part.
Proof: its Cesàro mean is zero while its mean square is strictly positive;
an exponential lower bound would force the mean square to vanish.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace polyak.Spectral.FiniteTrig

/-- Article: finite Cesàro average, including its harmless zeroth horizon. -/
def average (f : ℕ → ℝ) (N : ℕ) : ℝ := (N : ℝ)⁻¹*∑ m ∈ Finset.range N,f m

/-- Article: averaging commutes exactly with addition. -/
theorem average_add (f g : ℕ → ℝ) (N : ℕ) :
    average (fun m => f m+g m) N=average f N+average g N := by
  simp [average,Finset.sum_add_distrib,mul_add]

/-- Article: averaging commutes exactly with scalar multiplication. -/
theorem average_mul (a : ℝ) (f : ℕ → ℝ) (N : ℕ) :
    average (fun m => a*f m) N=a*average f N := by
  simp only [average,← Finset.mul_sum]
  ring

/-- Article: averaging commutes exactly with every finite family. -/
theorem average_sum {I : Type*} (S : Finset I) (f : I → ℕ → ℝ) (N : ℕ) :
    average (fun m => ∑ i ∈ S,f i m) N=∑ i ∈ S,average (f i) N := by
  unfold average
  rw [Finset.sum_comm,Finset.mul_sum]

/-- Article: averaging commutes with division by a fixed real scalar. -/
theorem average_div (f : ℕ → ℝ) (a : ℝ) (N : ℕ) :
    average (fun m => f m/a) N=average f N/a := by
  unfold average
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

/-- Article: partial sums of a nonconstant unit complex character are uniformly bounded. -/
theorem norm_geometric_sum_le {w : ℂ} (hw : ‖w‖=1) (hw1 : w ≠ 1) (N : ℕ) :
    ‖∑ m ∈ Finset.range N,w^m‖ ≤ 2/‖w-1‖ := by
  rw [geom_sum_eq hw1,norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  have hn := norm_sub_le (w^N) (1 : ℂ)
  norm_num [norm_pow,hw] at hn
  exact hn

/-- Article: a nonconstant unit complex character has zero Cesàro mean. -/
theorem unit_geometric_average {w : ℂ} (hw : ‖w‖=1) (hw1 : w ≠ 1) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • ∑ m ∈ Finset.range N,w^m) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm (fun N => ?_)
    (by simpa using hinv.mul_const (2/‖w-1‖))
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (norm_geometric_sum_le hw hw1 N) (by positivity)

/-- Article: weighted real character means vanish whenever the character is nonconstant. -/
theorem weighted_character_average (a w : ℂ) (hw : ‖w‖=1) (hw1 : w ≠ 1) :
    Tendsto (average (fun m => (a*w^m).re)) atTop (𝓝 0) := by
  have hz := (tendsto_const_nhds (x := a)).mul (unit_geometric_average hw hw1)
  simp only [mul_zero] at hz
  have hc := (Complex.continuous_re.tendsto (0 : ℂ)).comp hz
  simp only [Complex.zero_re,Function.comp_def] at hc
  convert hc using 1
  funext N
  unfold average
  rw [← Complex.re_sum,← Finset.mul_sum]
  simp only [Complex.real_smul,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,add_zero]
  ring

/-- Article: the real oscillatory sum of a finite probability spectrum. -/
def oscillation {J : Type*} [Fintype J] (w a : J → ℂ) (m : ℕ) : ℝ :=
  (∑ j,a j*w j^m).re

/-- Article: every finite sum of nonconstant unit characters has zero mean. -/
theorem oscillation_average {J : Type*} [Fintype J] (w a : J → ℂ)
    (hw : ∀ j,‖w j‖=1) (hw1 : ∀ j,w j ≠ 1) :
    Tendsto (average (oscillation w a)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ (fun j _ => weighted_character_average (a j) (w j) (hw j) (hw1 j))
  convert h using 1
  · funext N
    change average (fun m => (∑ j,a j*w j^m).re) N=∑ j,average (fun m => (a j*w j^m).re) N
    simp_rw [Complex.re_sum]
    exact average_sum _ _ _
  · simp

/-- Article: unit characters multiplied by their conjugates have product one. -/
theorem unit_mul_conj {w : ℂ} (hw : ‖w‖=1) : w*starRingEnd ℂ w=1 := by
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hw,one_pow,Complex.ofReal_one]

/-- Article: a unit character with positive imaginary part is nonconstant. -/
theorem unit_ne_one_of_im_pos {w : ℂ} (him : 0 < w.im) : w ≠ 1 := by
  intro h
  simp only [h,Complex.one_im,lt_self_iff_false] at him

/-- Article: sums of two strictly positive, sub-π frequencies are nonzero modulo 2π.
Proof: their unit-character product could equal one only if their imaginary parts had opposite signs. -/
theorem product_ne_one {w z : ℂ} (hz : ‖z‖=1) (hwim : 0 < w.im) (hzim : 0 < z.im) : w*z ≠ 1 := by
  intro h
  have he := congrArg (fun x : ℂ => x*starRingEnd ℂ z) h
  rw [mul_assoc,unit_mul_conj hz,mul_one,one_mul] at he
  have him := congrArg Complex.im he
  simp only [Complex.conj_im] at him
  linarith

/-- Article: distinct frequencies give nonconstant difference characters. -/
theorem difference_ne_one {w z : ℂ} (hz : ‖z‖=1) (hne : w ≠ z) : w*starRingEnd ℂ z ≠ 1 := by
  intro h
  have he := congrArg (fun x : ℂ => x*z) h
  have hconj : starRingEnd ℂ z*z=1 := by rw [mul_comm,unit_mul_conj hz]
  rw [mul_assoc,hconj,mul_one,one_mul] at he
  exact hne he

/-- Article: exact finite expansion of the squared real oscillation into sum and difference frequencies. -/
theorem oscillation_sq_expansion {J : Type*} [Fintype J] (w a : J → ℂ) (m : ℕ) :
    oscillation w a m^2 =
      ((∑ i,∑ j,(a i*a j*(w i*w j)^m).re)+
        ∑ i,∑ j,(a i*starRingEnd ℂ (a j)*(w i*starRingEnd ℂ (w j))^m).re)/2 := by
  classical
  let S := ∑ j,a j*w j^m
  have hsq : S.re^2=((S*S).re+(S*starRingEnd ℂ S).re)/2 := by
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
    ring
  have hp : S*S=∑ i,∑ j,a i*a j*(w i*w j)^m := by
    dsimp [S]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow]
    ring
  have hm : S*starRingEnd ℂ S=∑ i,∑ j,a i*starRingEnd ℂ (a j)*(w i*starRingEnd ℂ (w j))^m := by
    dsimp [S]
    simp only [map_sum,map_mul,map_pow]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow]
    ring
  rw [hp,hm] at hsq
  simpa only [Complex.re_sum,S,oscillation] using hsq

/-- Article: the mean square of a nonzero finite trigonometric sum is half its coefficient mass.
Proof: sum-frequency averages vanish, and only equal-frequency difference terms survive. -/
theorem oscillation_square_average {J : Type*} [Fintype J] (w a : J → ℂ)
    (hw : ∀ j,‖w j‖=1) (him : ∀ j,0 < (w j).im) (hinj : Function.Injective w) :
    Tendsto (average (fun m => oscillation w a m^2)) atTop
      (𝓝 ((∑ j,Complex.normSq (a j))/2)) := by
  classical
  have hp (i j : J) :
      Tendsto (average (fun m => (a i*a j*(w i*w j)^m).re)) atTop (𝓝 0) :=
    weighted_character_average _ _ (by rw [norm_mul,hw i,hw j,one_mul])
      (product_ne_one (hw j) (him i) (him j))
  have hm (i j : J) :
      Tendsto (average (fun m => (a i*starRingEnd ℂ (a j)*(w i*starRingEnd ℂ (w j))^m).re)) atTop
        (𝓝 (if i=j then Complex.normSq (a i) else 0)) := by
    by_cases hij : i=j
    · subst j
      simp only [unit_mul_conj (hw i),one_pow,mul_one,Complex.mul_conj,Complex.ofReal_re]
      exact (tendsto_const_nhds (x := Complex.normSq (a i))).cesaro
    · rw [ite_eq_right hij]
      exact weighted_character_average _ _ (by rw [norm_mul,Complex.norm_conj,hw i,hw j,one_mul])
        (difference_ne_one (hw j) (fun h => hij (hinj h)))
  have hplus := tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ (fun j _ => hp i j))
  have hminus := tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ (fun j _ => hm i j))
  have h := (hplus.add hminus).div_const 2
  have hdiag : (∑ i,∑ j,if i=j then Complex.normSq (a i) else 0)=∑ i,Complex.normSq (a i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [ite_eq_right (Ne.symm hj)]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  simp only [Finset.sum_const_zero,zero_add,hdiag] at h
  convert h using 1
  funext N
  simp only [oscillation_sq_expansion,average_div,average_add,average_sum]

/-- Article: a finite trigonometric sum is uniformly bounded by its coefficient mass. -/
theorem abs_oscillation_le {J : Type*} [Fintype J] (w a : J → ℂ)
    (hw : ∀ j,‖w j‖=1) (m : ℕ) : |oscillation w a m| ≤ ∑ j,‖a j‖ := by
  unfold oscillation
  calc
    _ ≤ ‖∑ j,a j*w j^m‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ j,‖a j*w j^m‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul,norm_pow,hw,one_pow,mul_one]

/-- Article: a bounded scalar with a small negative part has square controlled by its mean. -/
theorem square_le_of_lower {f M b : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b)
    (habs : |f| ≤ M) (hlower : -b ≤ f) : f^2 ≤ M*f+2*M*b := by
  have hsq : f^2 ≤ M*|f| := by
    have h := mul_le_mul_of_nonneg_right habs (abs_nonneg f)
    nlinarith [sq_abs f]
  have hpart : |f| ≤ f+2*b := by
    rcases le_total 0 f with h | h
    · rw [abs_of_nonneg h]
      linarith
    · rw [abs_of_nonpos h]
      linarith
  have hm := mul_le_mul_of_nonneg_left hpart hM
  nlinarith

/-- Article: a nonzero finite positive-frequency sum cannot have an exponentially vanishing negative part.
Proof: its mean square is strictly positive, while the lower bound and zero mean force it to zero. -/
theorem not_geometric_lower_bound {J : Type*} [Fintype J] (w a : J → ℂ)
    (hw : ∀ j,‖w j‖=1) (him : ∀ j,0 < (w j).im) (hinj : Function.Injective w)
    (ha : ∃ j,a j ≠ 0) (G r : ℝ) (hG : 0 ≤ G) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ¬ ∀ m : ℕ, -(G*r^m) ≤ oscillation w a m := by
  intro hlower
  let M : ℝ := ∑ j,‖a j‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hpoint (m : ℕ) : oscillation w a m^2 ≤ M*oscillation w a m+2*M*G*r^m := by
    have h := square_le_of_lower hM (mul_nonneg hG (pow_nonneg hr0 m))
      (abs_oscillation_le w a hw m) (hlower m)
    simpa only [mul_assoc] using h
  have havg (N : ℕ) : average (fun m => oscillation w a m^2) N ≤
      M*average (oscillation w a) N+2*M*G*average (fun m => r^m) N := by
    have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.range N) (fun m _ => hpoint m))
      (by positivity : 0 ≤ (N : ℝ)⁻¹)
    change average (fun m => oscillation w a m^2) N ≤
      average (fun m => M*oscillation w a m+2*M*G*r^m) N at hs
    simpa only [average_add,average_mul] using hs
  have hmean := oscillation_average w a hw (fun j => unit_ne_one_of_im_pos (him j))
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).cesaro
  have hmajor := (hmean.const_mul M).add (hpow.const_mul (2*M*G))
  simp only [mul_zero,zero_add] at hmajor
  have hsquare := oscillation_square_average w a hw him hinj
  have hnonpos : (∑ j,Complex.normSq (a j))/2 ≤ 0 :=
    le_of_tendsto_of_tendsto hsquare hmajor (Eventually.of_forall havg)
  obtain ⟨j,hj⟩ := ha
  have hpositive : 0 < ∑ i,Complex.normSq (a i) := by
    have hsingle : 0 < Complex.normSq (a j) := by
      rw [Complex.normSq_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr hj)
    exact hsingle.trans_le (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ j))
  linarith

/-- Article: advancing the origin multiplies each nonzero character coefficient by its unit phase. -/
theorem oscillation_succ {J : Type*} [Fintype J] (w a : J → ℂ) (m : ℕ) :
    oscillation w a (m+1)=oscillation w (fun j => a j*w j) m := by
  unfold oscillation
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

/-- Article: the finite-trigonometric contradiction in the original positive-lag exponential form.
Use: strict minimizer slack at all finite-support optimal spectra in Appendix A. -/
theorem not_exponential_lower_bound {J : Type*} [Fintype J] (w a : J → ℂ)
    (hw : ∀ j,‖w j‖=1) (him : ∀ j,0 < (w j).im) (hinj : Function.Injective w)
    (ha : ∃ j,a j ≠ 0) (G s : ℝ) (hG : 0 ≤ G) (hs : 0 < s) :
    ¬ ∀ m : ℕ, 1 ≤ m → -(G*Real.exp (-(m*s))) ≤ oscillation w a m := by
  intro hlower
  have hr0 : 0 ≤ Real.exp (-s) := (Real.exp_pos _).le
  have hr1 : Real.exp (-s) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have ha' : ∃ j,a j*w j ≠ 0 := by
    obtain ⟨j,hj⟩ := ha
    refine ⟨j,mul_ne_zero hj ?_⟩
    exact norm_ne_zero_iff.mp (by rw [hw j]; norm_num)
  apply not_geometric_lower_bound w (fun j => a j*w j) hw him hinj ha'
    (G*Real.exp (-s)) (Real.exp (-s)) (mul_nonneg hG hr0) hr0 hr1
  intro m
  have h := hlower (m+1) (by omega)
  rw [oscillation_succ] at h
  have he : Real.exp (-((m+1 : ℕ)*s))=Real.exp (-s)*Real.exp (-s)^m := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [he] at h
  simpa only [mul_assoc] using h

end polyak.Spectral.FiniteTrig
