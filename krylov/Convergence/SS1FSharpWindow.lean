import krylov.Convergence.SS1FSharpSource
import krylov.Convergence.SecantCubicSource
import krylov.Convergence.SS1FLeadingMatrix

/-!
Article: main_krylov, thm:ss1F, sharp whole observed-window estimates.
Use: retain the exact original T3 and L3/12 diagonal, the T3/2 adjacent
secant, and only a negligible newer-radius budget in all remaining entries.
Source: the genuine scalar third-derivative estimates and the true
symmetric two-entry spectral bound, with no model-error premise.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Functions krylov.Secant krylov.Methods krylov.LinearAlgebra
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] {p : ℕ}

/-- The exact proved source polynomial of a true corrected diagonal. -/
def sharpValueDiagonalBudget (B L C : ℝ) (a s x : E) : ℝ :=
  B*‖x‖+L/2*‖x‖^2+(B+L*‖a+s‖)*C*‖x-(a+s)‖+
    L*((1/12:ℝ)*‖s‖^2+(1/2:ℝ)*(1+C)*‖x-(a+s)‖*‖s‖+
      (1/2:ℝ)*‖x-(a+s)‖^2)

/- The genuine corrected normalized error is symmetric, including its
actual value-dependent diagonal. -/
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem ss1FNormalizedError_isSymm (f : E → ℝ) (G : E → E)
    (a s : Fin p → E) (l : Fin p → ℝ) :
    (ss1FNormalizedError f G a s l).IsSymm := by
  rw [ss1FNormalizedError_eq]
  exact ((latest_isSymm _).sub (Matrix.isHermitian_iff_isSymm.mp
    (crossGram_isHermitian (unitWindow s)))).sub (isSymm_diagonal _)

/-- Every actual off-diagonal error retains the genuine half-weight cubic
secant estimate at its newer endpoint pair. -/
theorem ss1F_offDiagonal_cubic_bound
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (L : ℝ≥0) (hLip : ∀ z∈S,∀ w∈S,∀ h:E,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L:ℝ)*‖z-w‖)
    {B : ℝ} (hB : 0≤B) (hbudget : ∀ h:E,‖h‖=1 → |(T 0).form h h h|≤B)
    (a s : Fin p → E) (l : Fin p → ℝ) (hs : ∀ i,s i≠0)
    (i j : Fin p) (hij : i≠j) (ha : a (max i j)∈S) (hb : a (max i j)+s (max i j)∈S)
    {R : ℝ} (hR : 0≤R) (har : ‖a (max i j)‖≤R) (hbr : ‖a (max i j)+s (max i j)‖≤R) :
    |ss1FNormalizedError f G a s l i j|≤
      B/2*(‖a (max i j)‖+‖a (max i j)+s (max i j)‖)+(L:ℝ)*R^2 := by
  let m := max i j
  let y := fun i=>G (a i+s i)-G (a i)
  let D := B/2*(‖a m‖+‖a m+s m‖)+(L:ℝ)*R^2
  have hr := secant_image_cubic_endpoint_bound G H T S hS h₀ hH₀ hG hT L hLip hB hbudget
    (a m) (a m+s m) ha hb hR har hbr
  rw [add_sub_cancel_left] at hr
  have he : unitWindowImages s y m-unitWindow s m=‖s m‖⁻¹ • (y m-s m) := by
    simp only [unitWindowImages,unitWindow,rescaleWindow,smul_sub]
  have hnorm : ‖unitWindowImages s y m-unitWindow s m‖≤D := by
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    apply (mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr (norm_nonneg _))).trans_eq
    change ‖s m‖⁻¹*(D*‖s m‖)=D
    field_simp [norm_ne_zero_iff.mpr (hs m)]
  rw [ss1FNormalizedError_eq,Matrix.sub_apply,diagonal_apply_ne _ hij,sub_zero,windowDataError_entry]
  have hi := norm_inner_le_norm (𝕜:=ℝ) (unitWindow s (min i j))
    (unitWindowImages s y m-unitWindow s m)
  rw [unitWindow_norm s hs,one_mul,Real.norm_eq_abs] at hi
  exact hi.trans hnorm

/- All newer corrected diagonals have a first-order newer radius and only
a second-order previous radius. The constant is irrelevant to the leading
00/01 coefficients, which are estimated separately. -/
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem sharp_diagonal_newer_radius_bound {B L C r₁ r₂ : ℝ}
    (hB : 0≤B) (hL : 0≤L) (hC : 0≤C) (hr₂ : 0≤r₂) (horder : r₂≤r₁)
    (a s x : E) (ha : ‖a‖≤r₁) (hb : ‖a+s‖≤r₂) (hx : ‖x‖≤r₂) :
    sharpValueDiagonalBudget B L C a s x≤
      B*(1+2*C)*r₂+L*(4+4*C)*(r₁+r₂)^2 := by
  let R := r₁+r₂
  have hR : 0≤R := by dsimp only [R]; linarith only [hr₂,horder]
  have hr : r₂≤R := by dsimp only [R]; linarith only [hr₂,horder]
  have hs : ‖s‖≤R := by
    have hh := norm_sub_le (a+s) a
    simp only [add_sub_cancel_left] at hh
    exact hh.trans (by dsimp only [R]; linarith only [ha,hb])
  have hd : ‖x-(a+s)‖≤2*r₂ := (norm_sub_le _ _).trans (by linarith only [hx,hb])
  have hdR : ‖x-(a+s)‖≤2*R := hd.trans (by linarith only [hr])
  have hx₂ : ‖x‖^2≤R^2 := by nlinarith only [hx,hr,norm_nonneg x,hR]
  have hs₂ : ‖s‖^2≤R^2 := by nlinarith only [hs,norm_nonneg s,hR]
  have hd₂ : ‖x-(a+s)‖^2≤4*R^2 := by nlinarith only [hdR,norm_nonneg (x-(a+s)),hR]
  have hbprod : ‖a+s‖*‖x-(a+s)‖≤2*R^2 := by
    have hh := mul_le_mul (hb.trans hr) hdR (norm_nonneg _) hR
    nlinarith only [hh]
  have hsprod : ‖x-(a+s)‖*‖s‖≤2*R^2 := by
    have hh := mul_le_mul hdR hs (norm_nonneg _) (by positivity : 0≤2*R)
    nlinarith only [hh]
  have hlinear : B*‖x‖+B*C*‖x-(a+s)‖≤B*(1+2*C)*r₂ := by
    have h₁ := mul_le_mul_of_nonneg_left hx hB
    have h₂ := mul_le_mul_of_nonneg_left hd (mul_nonneg hB hC)
    nlinarith only [h₁,h₂]
  have hpoly : (1/2:ℝ)*‖x‖^2+‖a+s‖*C*‖x-(a+s)‖+
      (1/12:ℝ)*‖s‖^2+(1/2:ℝ)*(1+C)*‖x-(a+s)‖*‖s‖+
      (1/2:ℝ)*‖x-(a+s)‖^2≤(4+4*C)*R^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hbprod hC
    have h₂ := mul_le_mul_of_nonneg_left hsprod (show 0≤(1/2:ℝ)*(1+C) by positivity)
    nlinarith only [hx₂,hs₂,hd₂,h₁,h₂,sq_nonneg R,mul_nonneg hC (sq_nonneg R)]
  have hscaled := mul_le_mul_of_nonneg_left hpoly hL
  dsimp only [sharpValueDiagonalBudget]
  change _≤B*(1+2*C)*r₂+L*(4+4*C)*R^2
  nlinarith only [hlinear,hscaled]

/- The true oldest source polynomial has precisely Cw*T3 times the
first-newer radius and L3/12 times the oldest radius squared; all the
remaining terms contain either a current radius or an extra newer factor. -/
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem sharp_diagonal_oldest_radius_bound {B L C r₀ r₁ r₂ : ℝ}
    (hB : 0≤B) (hL : 0≤L) (hC : 0≤C) (hr₂ : 0≤r₂)
    (horder : r₂≤r₁) (a s x : E) (ha : ‖a‖≤r₀) (hb : ‖a+s‖≤r₁) (hx : ‖x‖≤r₂) :
    sharpValueDiagonalBudget B L C a s x≤
      C*B*r₁+L/12*r₀^2+B*(1+C)*r₂+L*(4+4*C)*(r₀*r₁+r₁^2) := by
  have hr₁ : 0≤r₁ := hr₂.trans horder
  have hr₀ : 0≤r₀ := (norm_nonneg a).trans ha
  have hs : ‖s‖≤r₀+r₁ := by
    have hh := norm_sub_le (a+s) a
    simp only [add_sub_cancel_left] at hh
    exact hh.trans (by linarith only [ha,hb])
  have hd : ‖x-(a+s)‖≤r₂+r₁ := (norm_sub_le _ _).trans (add_le_add hx hb)
  have hd' : ‖x-(a+s)‖≤2*r₁ := hd.trans (by linarith only [horder])
  have hx₂ : ‖x‖^2≤r₁^2 := by nlinarith only [hx,horder,norm_nonneg x,hr₁]
  have hs₂ : ‖s‖^2≤(r₀+r₁)^2 := by nlinarith only [hs,norm_nonneg s,hr₀,hr₁]
  have hd₂ : ‖x-(a+s)‖^2≤4*r₁^2 := by nlinarith only [hd',norm_nonneg (x-(a+s)),hr₁]
  have hbprod : ‖a+s‖*‖x-(a+s)‖≤2*r₁^2 := by
    have hh := mul_le_mul hb hd' (norm_nonneg _) hr₁
    nlinarith only [hh]
  have hsprod : ‖x-(a+s)‖*‖s‖≤2*r₁*(r₀+r₁) :=
    mul_le_mul hd' hs (norm_nonneg _) (by positivity)
  have hlinear : B*‖x‖+B*C*‖x-(a+s)‖≤C*B*r₁+B*(1+C)*r₂ := by
    have h₁ := mul_le_mul_of_nonneg_left hx hB
    have h₂ := mul_le_mul_of_nonneg_left hd (mul_nonneg hB hC)
    nlinarith only [h₁,h₂]
  have hpoly : (1/2:ℝ)*‖x‖^2+‖a+s‖*C*‖x-(a+s)‖+
      (1/12:ℝ)*‖s‖^2+(1/2:ℝ)*(1+C)*‖x-(a+s)‖*‖s‖+
      (1/2:ℝ)*‖x-(a+s)‖^2≤r₀^2/12+(4+4*C)*(r₀*r₁+r₁^2) := by
    have h₁ := mul_le_mul_of_nonneg_left hbprod hC
    have h₂ := mul_le_mul_of_nonneg_left hsprod (show 0≤(1/2:ℝ)*(1+C) by positivity)
    nlinarith only [hx₂,hs₂,hd₂,h₁,h₂,mul_nonneg hr₀ hr₁,sq_nonneg r₁,
      mul_nonneg hC (mul_nonneg hr₀ hr₁),mul_nonneg hC (sq_nonneg r₁)]
  have hscaled := mul_le_mul_of_nonneg_left hpoly hL
  dsimp only [sharpValueDiagonalBudget]
  nlinarith only [hlinear,hscaled]

/- Apart from 00 and the adjacent symmetric pair, a non-diagonal latest
selector always uses a genuinely newer pair of index at least two. -/
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem max_other_window_index {n : ℕ} (i j : Fin (n+2)) (hij : i≠j)
    (h00 : ¬(i=0 ∧j=0)) (h01 : ¬((i=0 ∧j=1) ∨(i=1 ∧j=0))) :
    max i j≠0 ∧max i j≠1 := by
  have hi := le_max_left i j
  have hj := le_max_right i j
  constructor
  · intro hm
    apply h00
    exact ⟨le_antisymm (hi.trans (le_of_eq hm)) (Fin.zero_le _),
      le_antisymm (hj.trans (le_of_eq hm)) (Fin.zero_le _)⟩
  · intro hm
    have hi1 : i≤1 := hi.trans (le_of_eq hm)
    have hj1 : j≤1 := hj.trans (le_of_eq hm)
    have hone : (1:Fin (n+2)).val=1 := by simp
    have hi' : i=0 ∨i=1 := by
      by_cases hz : i=0
      · exact Or.inl hz
      · right
        apply Fin.ext
        change i.val≤(1:Fin (n+2)).val at hi1
        have hn : i.val≠0 := fun h=>hz (Fin.ext h)
        rw [hone] at hi1 ⊢
        omega
    have hj' : j=0 ∨j=1 := by
      by_cases hz : j=0
      · exact Or.inl hz
      · right
        apply Fin.ext
        change j.val≤(1:Fin (n+2)).val at hj1
        have hn : j.val≠0 := fun h=>hz (Fin.ext h)
        rw [hone] at hj1 ⊢
        omega
    rcases hi' with rfl|rfl
    · rcases hj' with rfl|rfl
      · exact hij rfl
      · exact h01 (Or.inl ⟨rfl,rfl⟩)
    · rcases hj' with rfl|rfl
      · exact h01 (Or.inr ⟨rfl,rfl⟩)
      · exact hij rfl

/-- The whole actual corrected matrix has its exact oldest diagonal and
half-weight adjacent cubic entry. Every other entry has only a newer
radius and a quadratic previous radius, also when T3 is zero. -/
theorem ss1F_sharp_window_bound {n : ℕ}
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (L : ℝ≥0) (hLip : ∀ z∈S,∀ w∈S,∀ h:E,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L:ℝ)*‖z-w‖)
    {B C r₁ r₂ : ℝ} (hB : 0≤B) (hC : 0≤C) (hr₂ : 0≤r₂) (horder : r₂≤r₁)
    (hbudget : ∀ h:E,‖h‖=1 → |(T 0).form h h h|≤B)
    (a s : Fin (n+2) → E) (l : Fin (n+2) → ℝ) (x : E)
    (ha : ∀ i,a i∈S) (hb : ∀ i,a i+s i∈S) (hx : x∈S)
    (hs : ∀ i,s i≠0)
    (hnew : ∀ i,i≠0 → ‖a i‖≤r₁)
    (hnewer : ∀ i,i≠0 → i≠1 → ‖a i‖≤r₂)
    (hend : ∀ i,i≠0 → ‖a i+s i‖≤r₂) (hxr : ‖x‖≤r₂)
    (hw : ∀ i,‖splitRemainder (a i) (s i) x (l i)‖≤C*‖x-(a i+s i)‖) :
    ‖ss1FNormalizedError f G a s l‖≤
      sharpValueDiagonalBudget B L C (a 0) (s 0) x+
        (B/2*(r₁+r₂)+(L:ℝ)*r₁^2)+
        ((n+2:ℕ):ℝ)*(B*(1+2*C)*r₂+(L:ℝ)*(4+4*C)*(r₁+r₂)^2) := by
  let X := ss1FNormalizedError f G a s l
  let ε := B*(1+2*C)*r₂+(L:ℝ)*(4+4*C)*(r₁+r₂)^2
  have hr₁ : 0≤r₁ := hr₂.trans horder
  have hε : 0≤ε := by dsimp only [ε]; positivity
  have hdiag (i : Fin (n+2)) : |X i i|≤sharpValueDiagonalBudget B L C (a i) (s i) x :=
    ss1FNormalizedError_diagonal_bound f G a s l hs i
      (ss1F_sharp_source_diagonal_bound f G H T S hS h₀ hH₀ hf hG hT L hLip hB hbudget
        (a i) (s i) x (ha i) (hb i) hx (l i) C (hw i))
  have hother : ∀ i j,¬(i=0 ∧j=0) → ¬((i=0 ∧j=1) ∨(i=1 ∧j=0)) → |X i j|≤ε := by
    intro i j h00 h01
    by_cases hij : i=j
    · subst j
      have hi : i≠0 := fun hi=>h00 ⟨hi,hi⟩
      exact (hdiag i).trans (sharp_diagonal_newer_radius_bound hB L.coe_nonneg hC hr₂ horder
        (a i) (s i) x (hnew i hi) (hend i hi) hxr)
    · obtain ⟨hm0,hm1⟩ := max_other_window_index i j hij h00 h01
      have he := ss1F_offDiagonal_cubic_bound f G H T S hS h₀ hH₀ hG hT L hLip hB hbudget a s l hs
        i j hij (ha _) (hb _) hr₂ (hnewer _ hm0 hm1) (hend _ hm0)
      have hraw : B/2*(‖a (max i j)‖+‖a (max i j)+s (max i j)‖)+(L:ℝ)*r₂^2≤
          B*r₂+(L:ℝ)*r₂^2 := by
        have hh := mul_le_mul_of_nonneg_left (add_le_add (hnewer _ hm0 hm1) (hend _ hm0))
          (show 0≤B/2 by positivity)
        nlinarith only [hh]
      have hfirst : B*r₂≤B*(1+2*C)*r₂ := by
        nlinarith only [mul_nonneg (mul_nonneg hB hC) hr₂]
      have hsq : r₂^2≤(r₁+r₂)^2 := by nlinarith only [hr₁,hr₂,mul_nonneg hr₁ hr₂,sq_nonneg r₁]
      have hsecond : (L:ℝ)*r₂^2≤(L:ℝ)*(4+4*C)*(r₁+r₂)^2 := by
        have h₁ := mul_le_mul_of_nonneg_left hsq L.coe_nonneg
        have h₂ : (L:ℝ)*(r₁+r₂)^2≤(L:ℝ)*(4+4*C)*(r₁+r₂)^2 := by
          nlinarith only [mul_nonneg L.coe_nonneg (sq_nonneg (r₁+r₂)),
            mul_nonneg (mul_nonneg L.coe_nonneg hC) (sq_nonneg (r₁+r₂))]
        exact h₁.trans h₂
      exact he.trans (hraw.trans (add_le_add hfirst hsecond))
  have hcross := ss1F_offDiagonal_cubic_bound f G H T S hS h₀ hH₀ hG hT L hLip hB hbudget a s l hs
    0 1 Fin.zero_ne_one (ha _) (hb _) hr₁ (by simpa using hnew 1 Fin.zero_ne_one.symm)
    (by simpa using (hend 1 Fin.zero_ne_one.symm).trans horder)
  have hc : |X 0 1|≤B/2*(r₁+r₂)+(L:ℝ)*r₁^2 := by
    apply hcross.trans
    have hh := mul_le_mul_of_nonneg_left
      (add_le_add (hnew 1 Fin.zero_ne_one.symm) (hend 1 Fin.zero_ne_one.symm))
      (show 0≤B/2 by positivity)
    simpa only [max_eq_right (show (0:Fin (n+2))≤1 from Fin.zero_le _)] using
      add_le_add hh (le_refl ((L:ℝ)*r₁^2))
  exact (oldest_leading_remainder_bound X (ss1FNormalizedError_isSymm f G a s l) hε hother).trans
    (add_le_add (add_le_add (hdiag 0) hc) le_rfl)

/-- The actual whole matrix has exactly the printed leading coefficients;
its explicit source remainder contains an additional newer-age factor.
In particular the estimate remains valid without division by T3 or L3. -/
theorem ss1F_sharp_age_bound {n : ℕ}
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (L : ℝ≥0) (hLip : ∀ z∈S,∀ w∈S,∀ h:E,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L:ℝ)*‖z-w‖)
    {B C r₀ r₁ r₂ : ℝ} (hB : 0≤B) (hC : 0≤C) (hr₂ : 0≤r₂) (horder : r₂≤r₁)
    (hbudget : ∀ h:E,‖h‖=1 → |(T 0).form h h h|≤B)
    (a s : Fin (n+2) → E) (l : Fin (n+2) → ℝ) (x : E)
    (ha : ∀ i,a i∈S) (hb : ∀ i,a i+s i∈S) (hx : x∈S)
    (hs : ∀ i,s i≠0)
    (ha₀ : ‖a 0‖≤r₀) (hb₀ : ‖a 0+s 0‖≤r₁)
    (hnew : ∀ i,i≠0 → ‖a i‖≤r₁)
    (hnewer : ∀ i,i≠0 → i≠1 → ‖a i‖≤r₂)
    (hend : ∀ i,i≠0 → ‖a i+s i‖≤r₂) (hxr : ‖x‖≤r₂)
    (hw : ∀ i,‖splitRemainder (a i) (s i) x (l i)‖≤C*‖x-(a i+s i)‖) :
    ‖ss1FNormalizedError f G a s l‖≤
      ((C+1/2)*B*r₁+(L:ℝ)/12*r₀^2)+
        (2+C+((n+2:ℕ):ℝ)*(1+2*C))*B*r₂+
        (4+4*C)*(L:ℝ)*r₀*r₁+
        ((4+4*C)*(1+4*((n+2:ℕ):ℝ))+1)*(L:ℝ)*r₁^2 := by
  have hr₁ : 0≤r₁ := hr₂.trans horder
  have hwhole := ss1F_sharp_window_bound f G H T S hS h₀ hH₀ hf hG hT L hLip hB hC hr₂ horder
    hbudget a s l x ha hb hx hs hnew hnewer hend hxr hw
  have hold := sharp_diagonal_oldest_radius_bound hB L.coe_nonneg hC hr₂ horder
    (a 0) (s 0) x ha₀ hb₀ hxr
  have h₁ := add_le_add (add_le_add hold (le_refl (B/2*(r₁+r₂)+(L:ℝ)*r₁^2)))
    (le_refl (((n+2:ℕ):ℝ)*(B*(1+2*C)*r₂+(L:ℝ)*(4+4*C)*(r₁+r₂)^2)))
  apply (hwhole.trans h₁).trans
  have hsq : (r₁+r₂)^2≤4*r₁^2 := by
    nlinarith only [hr₂,horder,mul_nonneg hr₂ (sub_nonneg.mpr horder)]
  have hscaled := mul_le_mul_of_nonneg_left hsq
    (show 0≤((n+2:ℕ):ℝ)*(L:ℝ)*(4+4*C) by positivity)
  nlinarith only [hscaled,mul_nonneg hB hr₂]

end
end krylov.Convergence
