import polyak.Dynamics.QuadraticRate
import chebyshev1.Background.HeavyBallLimit

/-! The Polyak parameters globally minimize the actual quadratic characteristic-root
radius over all real constant step sizes and momenta.  No stability restriction on a
competitor is needed.  The root radius is the supremum of actual complex-root norms,
not a chosen upper bound for a recurrence. -/
namespace chebyshev1.Background
noncomputable section
open polyak.Dynamics

private theorem quadratic_root_norm_bound (a β : ℝ) {z : ℂ}
    (hz : z^2 - (a : ℂ)*z + (β : ℂ)=0) :
    ‖z‖ ≤ 1+|a|+|β| := by
  have he : z^2=(a : ℂ)*z-(β : ℂ) := by linear_combination hz
  have hn : ‖z‖^2 ≤ |a| * ‖z‖+|β| := by
    calc
      ‖z‖^2 = ‖z^2‖ := (norm_pow z 2).symm
      _ = ‖(a : ℂ)*z-(β : ℂ)‖ := congrArg norm he
      _ ≤ ‖(a : ℂ)*z‖+‖(β : ℂ)‖ := norm_sub_le _ _
      _ = _ := by simp [Complex.norm_real, Real.norm_eq_abs]
  by_contra hh
  have hh : 1+|a|+|β| < ‖z‖ := lt_of_not_ge hh
  have h1 : 1 < ‖z‖ := by linarith [abs_nonneg a,abs_nonneg β]
  have hp := mul_nonneg (show 0 ≤ ‖z‖-1 by linarith) (abs_nonneg β)
  have hd := mul_pos (show 0 < ‖z‖ by linarith)
    (show 0 < ‖z‖-(1+|a|+|β|) by linarith)
  nlinarith

/-- The actual root set is bounded for every real constant tuning, including unstable ones. -/
theorem heavyBall_rootNorms_bddAbove (μ L α β : ℝ) :
    BddAbove (quadraticRootNorms μ L α β) := by
  refine ⟨1+|1+β|+|α| * (|μ|+|L|)+|β|, ?_⟩
  rintro r ⟨lam,hlam,z,hz,rfl⟩
  have hlamabs : |lam| ≤ |μ|+|L| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le μ,abs_nonneg L,hlam.1]
    · linarith [le_abs_self L,abs_nonneg μ,hlam.2]
  have ha : |1+β-α*lam| ≤ |1+β|+|α| * (|μ|+|L|) := by
    calc
      _ ≤ |1+β|+|α*lam| := abs_sub _ _
      _ = |1+β|+|α| * |lam| := by rw [abs_mul]
      _ ≤ _ := by gcongr
  exact (quadratic_root_norm_bound _ _ hz).trans (by linarith)

/-- Every actual characteristic-root modulus is below the supremal rate. -/
theorem heavyBall_root_norm_le_rate (μ L α β lam : ℝ)
    (hlam : lam ∈ Set.Icc μ L) {z : ℂ}
    (hz : z^2-((1+β-α*lam : ℝ) : ℂ)*z+(β : ℂ)=0) :
    ‖z‖ ≤ quadraticRate μ L α β :=
  le_csSup (heavyBall_rootNorms_bddAbove μ L α β) ⟨lam,hlam,z,hz,rfl⟩

private theorem quadratic_disk_conditions {a β r : ℝ} (hr : 0 ≤ r)
    (hroot : ∀ z : ℂ, z^2-(a : ℂ)*z+(β : ℂ)=0 → ‖z‖ ≤ r) :
    β ≤ r^2 ∧ 0 ≤ r^2-a*r+β ∧ 0 ≤ r^2+a*r+β := by
  obtain ⟨z,hz⟩ := exists_complex_quadratic_root a β
  let w : ℂ := (a : ℂ)-z
  have hw : w^2-(a : ℂ)*w+(β : ℂ)=0 := by
    dsimp [w]
    linear_combination hz
  have hp : z*w=(β : ℂ) := by dsimp [w]; linear_combination -hz
  have hzle := hroot z hz
  have hwle := hroot w hw
  have hb : β ≤ r^2 := by
    have hh := congrArg norm hp
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs] at hh
    have hmul := mul_le_mul hzle hwle (norm_nonneg w) hr
    nlinarith [le_abs_self β]
  refine ⟨hb,?_⟩
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.sub_re,Complex.add_re,Complex.mul_re,pow_two,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.zero_re] at hre
  simp only [Complex.sub_im,Complex.add_im,Complex.mul_im,pow_two,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,Complex.zero_im] at him
  by_cases hi : z.im=0
  · have hzre : |z.re| ≤ r := (Complex.abs_re_le_norm z).trans hzle
    have hwre : |a-z.re| ≤ r := by
      simpa only [w,Complex.sub_re,Complex.ofReal_re] using
        (Complex.abs_re_le_norm w).trans hwle
    have hp' : z.re^2-a*z.re+β=0 := by simpa [hi,sq] using hre
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr (abs_le.mp hzre).2)
        (sub_nonneg.mpr (abs_le.mp hwre).2)]
    · nlinarith [mul_nonneg (show 0 ≤ r+z.re by linarith [(abs_le.mp hzre).1])
        (show 0 ≤ r+(a-z.re) by linarith [(abs_le.mp hwre).1])]
  · have hlin : 2*z.re-a=0 :=
      (mul_eq_zero.mp (show z.im*(2*z.re-a)=0 by nlinarith)).resolve_left hi
    have ha : a=2*z.re := by linarith
    rw [ha] at hre ⊢
    constructor <;> nlinarith [sq_nonneg (r-z.re),sq_nonneg (r+z.re),sq_nonneg z.im]

private theorem polyakQ_balance {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    (L-μ)*(1+(polyakQ μ L)^2)=2*(L+μ)*polyakQ μ L := by
  have hA := polyak_normalizedA hμ hL
  have hB := polyak_normalizedB hμ hL
  dsimp [normalizedA,polyakBeta] at hA
  dsimp [normalizedB] at hB
  linear_combination (L-μ)*hA+(L+μ)*hB

/-- No real constant heavy-ball tuning has a smaller worst-curvature root radius.
The comparison includes negative momenta, nonpositive step sizes and unstable tunings. -/
theorem heavyBall_rate_lower {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) (α β : ℝ) :
    polyakQ μ L ≤ quadraticRate μ L α β := by
  let R := quadraticRate μ L α β
  let q := polyakQ μ L
  have hq : 0 < q := polyakQ_pos hμ hL
  have hq1 : q < 1 := polyakQ_lt_one hμ hL
  obtain ⟨z,hz⟩ := exists_complex_quadratic_root (1+β-α*μ) β
  have hR : 0 ≤ R := (norm_nonneg z).trans
    (heavyBall_root_norm_le_rate μ L α β μ ⟨le_rfl,hL.le⟩ hz)
  by_contra hbad
  have hRq : R < q := lt_of_not_ge hbad
  have hc (lam : ℝ) (hlam : lam ∈ Set.Icc μ L) :=
    quadratic_disk_conditions hR (fun z hz => heavyBall_root_norm_le_rate μ L α β lam hlam hz)
  have hb : β < q^2 := lt_of_le_of_lt (hc μ ⟨le_rfl,hL.le⟩).1 (by nlinarith)
  have hcq (lam : ℝ) (hlam : lam ∈ Set.Icc μ L) :=
    quadratic_disk_conditions hq.le (fun z hz =>
      (heavyBall_root_norm_le_rate μ L α β lam hlam hz).trans hRq.le)
  have hm := (hcq μ ⟨le_rfl,hL.le⟩).2.1
  have hl := (hcq L ⟨hL.le,le_rfl⟩).2.2
  have hend : 0 ≤ (L+μ)*(q^2+β)-(L-μ)*q*(1+β) := by
    have hm' := mul_nonneg (hμ.trans hL).le hm
    have hl' := mul_nonneg hμ.le hl
    nlinarith
  have hbalance : (L-μ)*(1+q^2)=2*(L+μ)*q := polyakQ_balance hμ hL
  have hprod := mul_nonneg hend (show 0 ≤ 1+q^2 by positivity)
  have hid : ((L+μ)*(q^2+β)-(L-μ)*q*(1+β))*(1+q^2) =
      (L+μ)*(1-q^2)*(β-q^2) := by
    linear_combination -q*(1+β)*hbalance
  rw [hid] at hprod
  have hneg : (L+μ)*(1-q^2)*(β-q^2) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (by linarith) (by nlinarith)) (by linarith)
  exact (not_lt_of_ge hprod) hneg

/-- Quantified optimality over the whole plane of constant parameters, with attainment. -/
theorem heavyBall_optimal_parameters {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    quadraticRate μ L (4/(Real.sqrt L+Real.sqrt μ)^2)
        (((Real.sqrt L-Real.sqrt μ)/(Real.sqrt L+Real.sqrt μ))^2) =
      (Real.sqrt L-Real.sqrt μ)/(Real.sqrt L+Real.sqrt μ) ∧
    ∀ α β : ℝ,
      quadraticRate μ L (4/(Real.sqrt L+Real.sqrt μ)^2)
        (((Real.sqrt L-Real.sqrt μ)/(Real.sqrt L+Real.sqrt μ))^2) ≤
      quadraticRate μ L α β := by
  change quadraticRate μ L (polyakAlpha μ L) (polyakBeta μ L)=polyakQ μ L ∧
    ∀ α β : ℝ, quadraticRate μ L (polyakAlpha μ L) (polyakBeta μ L) ≤
      quadraticRate μ L α β
  rw [polyak_quadraticRate hμ hL]
  exact ⟨rfl,heavyBall_rate_lower hμ hL⟩

/-- The optimal factor is a genuine minimum of the attained characteristic-root radii. -/
theorem heavyBall_rate_isLeast {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    IsLeast {r : ℝ | ∃ α β : ℝ, r=quadraticRate μ L α β} (polyakQ μ L) := by
  refine ⟨⟨polyakAlpha μ L,polyakBeta μ L,(polyak_quadraticRate hμ hL).symm⟩,?_⟩
  rintro r ⟨α,β,rfl⟩
  exact heavyBall_rate_lower hμ hL α β

/-- The minimizing tuning is unique, even among arbitrary real competitors. -/
theorem heavyBall_rate_eq_iff {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    quadraticRate μ L α β=polyakQ μ L ↔
      α=polyakAlpha μ L ∧ β=polyakBeta μ L := by
  constructor
  · intro hrate
    let q := polyakQ μ L
    have hq : 0 < q := polyakQ_pos hμ hL
    have hq1 : q < 1 := polyakQ_lt_one hμ hL
    have hc (lam : ℝ) (hlam : lam ∈ Set.Icc μ L) :=
      quadratic_disk_conditions hq.le (fun z hz => by
        have hh := heavyBall_root_norm_le_rate μ L α β lam hlam hz
        simpa only [hrate] using hh)
    have hb := (hc μ ⟨le_rfl,hL.le⟩).1
    have hm := (hc μ ⟨le_rfl,hL.le⟩).2.1
    have hl := (hc L ⟨hL.le,le_rfl⟩).2.2
    have hend : 0 ≤ (L+μ)*(q^2+β)-(L-μ)*q*(1+β) := by
      have hm' := mul_nonneg (hμ.trans hL).le hm
      have hl' := mul_nonneg hμ.le hl
      nlinarith
    have hbalance : (L-μ)*(1+q^2)=2*(L+μ)*q := polyakQ_balance hμ hL
    have hprod := mul_nonneg hend (show 0 ≤ 1+q^2 by positivity)
    have hid : ((L+μ)*(q^2+β)-(L-μ)*q*(1+β))*(1+q^2) =
        (L+μ)*(1-q^2)*(β-q^2) := by
      linear_combination -q*(1+β)*hbalance
    rw [hid] at hprod
    have hcoef : 0 < (L+μ)*(1-q^2) := mul_pos (by linarith) (by nlinarith)
    have hbge : 0 ≤ β-q^2 := nonneg_of_mul_nonneg_right hprod hcoef
    have hbeq : β=q^2 := by linarith
    have hzero : L*(q^2-(1+β-α*μ)*q+β)+μ*(q^2+(1+β-α*L)*q+β)=0 := by
      rw [hbeq]
      linear_combination -q*hbalance
    have hpm : q^2-(1+β-α*μ)*q+β=0 := by
      have hleft : L*(q^2-(1+β-α*μ)*q+β) ≤ 0 := by
        have hright := mul_nonneg hμ.le hl
        linarith
      have hh := nonpos_of_mul_nonpos_right hleft (hμ.trans hL)
      exact le_antisymm hh hm
    have hA := polyak_normalizedA hμ hL
    have hB := polyak_normalizedB hμ hL
    dsimp [normalizedA,polyakBeta] at hA
    dsimp [normalizedB] at hB
    have haμ : 1+q^2-polyakAlpha μ L*μ=2*q := by dsimp [q]; nlinarith
    have haμq := congrArg (fun x : ℝ => x*q) haμ
    have halpha : (α-polyakAlpha μ L)*(μ*q)=0 := by
      rw [hbeq] at hpm
      nlinarith
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp halpha).resolve_right (mul_pos hμ hq).ne'),hbeq⟩
  · rintro ⟨rfl,rfl⟩
    exact polyak_quadraticRate hμ hL

end
end chebyshev1.Background
