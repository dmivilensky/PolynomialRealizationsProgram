import krylov.Tensor.CubicBanach

/-!
Article: main_krylov, thm:Fexact, the diagonal fourth-derivative bound.
Use: Banach's diagonal-to-mixed identity for genuine symmetric quartic
forms on finite dimensional real Hilbert spaces.
Source: Banach (1938). The compact maximizing tuple is chosen to maximize
the norm of its vector sum. Polarization and pair normalization force its
vectors to coincide. No fourth-order norm identity is assumed.
-/

namespace krylov.Tensor
noncomputable section
open NormedSpace
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Fix the operator-space instances through three curried codomains.
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ)
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ)

/-- A genuine symmetric continuous quadrilinear scalar form.
Article: main_krylov, thm:Fexact, the fourth differential. -/
structure SymmetricQuartic (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  form : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ
  swap₁ : ∀ a b c d, form a b c d=form b a c d
  swap₂ : ∀ a b c d, form a b c d=form a c b d
  swap₃ : ∀ a b c d, form a b c d=form a b d c

/-- Continuity of the actual quadrilinear evaluation on vector quadruples.
Article: main_krylov, thm:Fexact, compact maximization in Banach's theorem. -/
theorem continuous_quartic_tuple (Q : SymmetricQuartic E) :
    Continuous (fun p : (E×E)×(E×E) => |Q.form p.1.1 p.1.2 p.2.1 p.2.2|) := by
  exact (((((Q.form.continuous.comp continuous_fst.fst).clm_apply continuous_fst.snd).clm_apply
    continuous_snd.fst).clm_apply continuous_snd.snd)).abs

/-- Repeated-pair bounds follow from a true mixed unit bound by homogeneity.
Article: main_krylov, thm:Fexact, quartic Banach identity. -/
theorem quartic_repeated_bound (Q : SymmetricQuartic E) (M : ℝ)
    (h : ∀ u v z w : E, ‖u‖=1 → ‖v‖=1 → ‖z‖=1 → ‖w‖=1 → |Q.form u v z w|≤M)
    (x z w : E) (hz : ‖z‖=1) (hw : ‖w‖=1) :
    |Q.form x x z w|≤M*‖x‖^2 := by
  by_cases hx : x=0
  · simp [hx]
  · have hb := h (normalize x) (normalize x) z w (norm_normalize hx) (norm_normalize hx) hz hw
    have he : Q.form x x z w=‖x‖^2*Q.form (normalize x) (normalize x) z w := by
      conv_lhs => rw [← norm_smul_normalize x]
      simp only [map_smul,smul_apply,smul_eq_mul]
      ring
    rw [he,abs_mul,abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg ‖x‖)]

/-- A zero first argument gives the actual scalar zero, with the curried
operator instances fixed inside this module.
Article: main_krylov, thm:Fexact, quartic tensor algebra. -/
theorem quartic_zero_first (Q : SymmetricQuartic E) (y z w : E) :
    Q.form 0 y z w=0 := by
  rw [map_zero]
  rfl

/-- Exact first-slot addition after evaluation of the iterated operator maps.
Article: main_krylov, thm:Fexact, quartic tensor algebra. -/
theorem quartic_add_first (Q : SymmetricQuartic E) (a b y z w : E) :
    Q.form (a+b) y z w=Q.form a y z w+Q.form b y z w := by
  rw [map_add]
  rfl

/-- Exact first-slot subtraction after full scalar evaluation.
Article: main_krylov, thm:Fexact, quartic tensor algebra. -/
theorem quartic_sub_first (Q : SymmetricQuartic E) (a b y z w : E) :
    Q.form (a-b) y z w=Q.form a y z w-Q.form b y z w := by
  rw [map_sub]
  rfl

/-- Negating the first slot negates the actual scalar evaluation.
Article: main_krylov, thm:Fexact, quartic tensor algebra. -/
theorem quartic_neg_first (Q : SymmetricQuartic E) (x y z w : E) :
    Q.form (-x) y z w= -Q.form x y z w := by
  rw [map_neg]
  rfl

/-- Negating the second slot negates the actual scalar evaluation.
Article: main_krylov, thm:Fexact, quartic tensor algebra. -/
theorem quartic_neg_second (Q : SymmetricQuartic E) (x y z w : E) :
    Q.form x (-y) z w= -Q.form x y z w := by
  rw [map_neg]
  rfl

/-- Exact quadratic polarization in the first two slots of the quartic.
Article: main_krylov, thm:Fexact, quartic Banach identity. -/
theorem quartic_polarization (Q : SymmetricQuartic E) (x y z w : E) :
    Q.form (x+y) (x+y) z w-Q.form (x-y) (x-y) z w=4*Q.form x y z w := by
  rw [quartic_add_first,quartic_sub_first]
  simp only [map_add,map_sub,add_apply,sub_apply]
  rw [Q.swap₁ y x z w]
  ring

set_option maxHeartbeats 800000 in
/-- A maximum tensor tuple having the largest vector sum has coinciding
first two vectors.
Article: main_krylov, thm:Fexact, quartic Banach identity.
Proof: polarization preserves maximality when a pair is replaced by two
normalized copies of its sum. The secondary maximum strictly improves
unless the pair coincides. The antipodal case is excluded by sign flips. -/
theorem quartic_max_sum_pair_eq (Q : SymmetricQuartic E) (M : ℝ)
    (hbound : ∀ u v z w : E, ‖u‖=1 → ‖v‖=1 → ‖z‖=1 → ‖w‖=1 → |Q.form u v z w|≤M)
    (x y z w : E) (hx : ‖x‖=1) (hy : ‖y‖=1) (hz : ‖z‖=1) (hw : ‖w‖=1)
    (hQ : |Q.form x y z w|=M)
    (hmax : ∀ u v z' w' : E, ‖u‖=1 → ‖v‖=1 → ‖z'‖=1 → ‖w'‖=1 →
      |Q.form u v z' w'|=M → ‖u+v+z'+w'‖≤‖x+y+z+w‖) : x=y := by
  let R := z+w
  have hM : 0≤M := hQ ▸ abs_nonneg _
  have hPn : x+y≠0 := by
    intro hzero
    have hyneg : y=-x := by
      simpa only [← add_assoc,neg_add_cancel,zero_add,add_zero] using
        congrArg (fun v : E => -x+v) hzero
    have h1 := hmax x (-y) z w hx (by simpa only [norm_neg] using hy) hz hw
      (by simpa only [quartic_neg_second,abs_neg] using hQ)
    have h2 := hmax (-x) y z w (by simpa only [norm_neg] using hx) hy hz hw
      (by simpa only [quartic_neg_first,abs_neg] using hQ)
    have hold : x+y+z+w=R := by dsimp only [R];rw [hzero,zero_add]
    have hplus : x+-y+z+w=(2:ℝ) • x+R := by rw [hyneg];dsimp only [R];module
    have hminus : -x+y+z+w=(-2:ℝ) • x+R := by rw [hyneg];dsimp only [R];module
    rw [hold,hplus] at h1
    rw [hold,hminus] at h2
    have hs1 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h1
    have hs2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h2
    have hn1 := norm_add_sq_real ((2:ℝ) • x) R
    have hn2 := norm_add_sq_real ((-2:ℝ) • x) R
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2),
      abs_of_neg (by norm_num : (-2:ℝ)<0),hx,inner_smul_left,conj_trivial] at hn1 hn2
    nlinarith
  let u := normalize (x+y)
  let r := ‖x+y‖
  have hr : 0<r := norm_pos_iff.mpr hPn
  have hu : ‖u‖=1 := norm_normalize hPn
  have hsum : ‖x+y‖^2+‖x-y‖^2=4 := by
    rw [norm_add_sq_real,norm_sub_sq_real,hx,hy]
    ring
  have hp := quartic_repeated_bound Q M hbound (x+y) z w hz hw
  have hm := quartic_repeated_bound Q M hbound (x-y) z w hz hw
  have hpol := quartic_polarization Q x y z w
  have hpEq : |Q.form (x+y) (x+y) z w|=M*‖x+y‖^2 := by
    rcases eq_or_eq_neg_of_abs_eq hQ with hsign | hsign
    · have hpu := (abs_le.mp hp).2
      have hml := (abs_le.mp hm).1
      have he : Q.form (x+y) (x+y) z w=M*‖x+y‖^2 := by nlinarith
      rw [he,abs_of_nonneg (by positivity)]
    · have hpl := (abs_le.mp hp).1
      have hmu := (abs_le.mp hm).2
      have he : Q.form (x+y) (x+y) z w=-(M*‖x+y‖^2) := by nlinarith
      rw [he,abs_neg,abs_of_nonneg (by positivity)]
  have huM : |Q.form u u z w|=M := by
    have he : Q.form (x+y) (x+y) z w=r^2*Q.form u u z w := by
      conv_lhs => rw [← norm_smul_normalize (x+y)]
      simp only [map_smul,smul_apply,smul_eq_mul]
      dsimp only [r,u]
      ring
    rw [he,abs_mul,abs_of_nonneg (sq_nonneg _)] at hpEq
    change r^2*|Q.form u u z w|=M*r^2 at hpEq
    nlinarith [sq_pos_of_pos hr]
  have hnew := hmax u u z w hu hu hz hw huM
  have hflip := hmax (-x) (-y) z w (by simpa only [norm_neg] using hx)
    (by simpa only [norm_neg] using hy) hz hw
    (by simpa only [quartic_neg_first,quartic_neg_second,neg_neg] using hQ)
  have hPr : r • u=x+y := norm_smul_normalize _
  have hold : x+y+z+w=r • u+R := by rw [hPr];dsimp only [R];abel
  have hnewEq : u+u+z+w=(2:ℝ) • u+R := by dsimp only [R];module
  have hflipEq : -x+-y+z+w=(-r) • u+R := by rw [neg_smul,hPr];dsimp only [R];module
  rw [hold,hnewEq] at hnew
  rw [hold,hflipEq] at hflip
  have hnewSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnew
  have hflipSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hflip
  have holdSq := norm_add_sq_real (r • u) R
  have hnewNorm := norm_add_sq_real ((2:ℝ) • u) R
  have hflipNorm := norm_add_sq_real ((-r) • u) R
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hr,abs_neg,hu,mul_one,
    inner_smul_left,conj_trivial] at holdSq hflipNorm
  norm_num only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2),
    hu,mul_one,inner_smul_left,conj_trivial] at hnewNorm
  have hrt : 0≤r*inner ℝ u R := by nlinarith
  have ht : 0≤ inner ℝ u R := (mul_nonneg_iff_of_pos_left hr).mp hrt
  by_contra hne
  have hdiff : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hrlt : r<2 := by change r^2+‖x-y‖^2=4 at hsum;nlinarith [sq_pos_of_pos hdiff]
  have hprod := mul_nonneg (by linarith : 0≤2-r) ht
  nlinarith

end
end krylov.Tensor
