import krylov.Functions.CubicSegment
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

/-!
Article: main_krylov, thm:Hp, apD:lem-binary(a), thm:Fexact.
Use: Banach's diagonal-to-mixed norm identity for real symmetric cubic
forms on finite dimensional Hilbert spaces.
Source: Banach (1938). The proof uses compactness and polarization:
among maximum repeated-slot pairs choose one of maximum alignment;
normalizing its sum improves alignment unless the two vectors coincide.
-/

namespace krylov.Tensor
noncomputable section
open krylov.Functions NormedSpace
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Continuity of the genuine repeated-slot tensor evaluation.
Article: main_krylov, thm:Hp, compact maximization in Banach's theorem. -/
theorem continuous_cubic_pair (T : SymmetricCubic E) :
    Continuous (fun p : E×E => |T.form p.1 p.1 p.2|) := by
  exact (((T.form.continuous.comp continuous_fst).clm_apply continuous_fst).clm_apply
    continuous_snd).abs

/-- Unit repeated-slot bounds extend by exact quadratic homogeneity in
that repeated vector. Article: main_krylov, thm:Hp, Banach's theorem. -/
theorem repeated_homogeneous_bound (T : SymmetricCubic E) (M : ℝ)
    (h : ∀ x y : E, ‖x‖=1 → ‖y‖=1 → |T.form x x y|≤M)
    (x y : E) (hy : ‖y‖=1) : |T.form x x y|≤M*‖x‖^2 := by
  by_cases hx : x=0
  · simp [hx]
  · have hn := norm_normalize hx
    have hb := h (normalize x) y hn hy
    have he : T.form x x y=‖x‖^2*T.form (normalize x) (normalize x) y := by
      conv_lhs => rw [← norm_smul_normalize x]
      simp only [map_smul,smul_apply,smul_eq_mul]
      ring
    rw [he,abs_mul,abs_of_nonneg (sq_nonneg ‖x‖)]
    nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg ‖x‖)]

/-- The exact quadratic polarization identity for the repeated slots.
Article: main_krylov, thm:Hp, Banach's diagonal-to-mixed identity. -/
theorem cubic_polarization (T : SymmetricCubic E) (x y z : E) :
    T.form (x+y) (x+y) z-T.form (x-y) (x-y) z=4*T.form x y z := by
  simp only [map_add,map_sub,add_apply,sub_apply]
  rw [T.swap₁ y x z]
  ring

/-- A genuine maximizing repeated-slot pair exists in every nontrivial finite
real Hilbert space. Article: main_krylov, thm:Hp, Banach's theorem.
Proof: the unit spheres are compact and the actual tensor is continuous. -/
theorem exists_repeated_max [FiniteDimensional ℝ E] [Nontrivial E]
    (T : SymmetricCubic E) :
    ∃ x y : E, ‖x‖=1 ∧ ‖y‖=1 ∧
      ∀ u v : E, ‖u‖=1 → ‖v‖=1 → |T.form u u v|≤|T.form x x y| := by
  let K : Set (E×E) := Metric.sphere (0:E) 1 ×ˢ Metric.sphere (0:E) 1
  have hK : IsCompact K := (isCompact_sphere (0:E) 1).prod (isCompact_sphere (0:E) 1)
  obtain ⟨e,he⟩ := exists_norm_eq E (show (0:ℝ)≤1 by norm_num)
  have heK : (e,e)∈K := by simpa [K,Metric.mem_sphere,dist_zero_right] using And.intro he he
  obtain ⟨p,hp,hmax⟩ := hK.exists_isMaxOn ⟨(e,e),heK⟩ (continuous_cubic_pair T).continuousOn
  have hp' : ‖p.1‖=1 ∧ ‖p.2‖=1 := by simpa [K,Metric.mem_sphere,dist_zero_right] using hp
  refine ⟨p.1,p.2,hp'.1,hp'.2,?_⟩
  intro u v hu hv
  exact hmax (a := (u,v)) (by simpa [K,Metric.mem_sphere,dist_zero_right] using And.intro hu hv)

/-- A maximum repeated-slot pair can be chosen with coinciding vectors.
Article: main_krylov, thm:Hp, Banach's theorem for symmetric cubics.
Proof: maximize the alignment among all maximum pairs. Polarization forces
its normalized sum to be another maximum pair, with larger alignment
unless the two vectors already coincide. -/
theorem exists_diagonal_max_of_repeated [FiniteDimensional ℝ E]
    (T : SymmetricCubic E) (M : ℝ)
    (hbound : ∀ x y : E, ‖x‖=1 → ‖y‖=1 → |T.form x x y|≤M)
    (hex : ∃ x y : E, ‖x‖=1 ∧ ‖y‖=1 ∧ |T.form x x y|=M) :
    ∃ x : E, ‖x‖=1 ∧ |T.form x x x|=M := by
  let K : Set (E×E) := Metric.sphere (0:E) 1 ×ˢ Metric.sphere (0:E) 1
  let A : Set (E×E) := K ∩ {p | |T.form p.1 p.1 p.2|=M}
  have hK : IsCompact K := (isCompact_sphere (0:E) 1).prod (isCompact_sphere (0:E) 1)
  have hA : IsCompact A := hK.inter_right (isClosed_eq (continuous_cubic_pair T) continuous_const)
  obtain ⟨u,v,hu,hv,huv⟩ := hex
  have hAne : A.Nonempty := by
    refine ⟨(u,v),?_,huv⟩
    simpa [K,Metric.mem_sphere,dist_zero_right] using And.intro hu hv
  obtain ⟨p,hp,hmax⟩ := hA.exists_isMaxOn hAne
    (show Continuous (fun q : E×E => inner ℝ q.1 q.2) from
      continuous_fst.inner continuous_snd).continuousOn
  let x := p.1
  let y := p.2
  have hx : ‖x‖=1 := by simpa [K,Metric.mem_sphere,dist_zero_right,x] using hp.1.1
  have hy : ‖y‖=1 := by simpa [K,Metric.mem_sphere,dist_zero_right,y] using hp.1.2
  have hxy : |T.form x x y|=M := hp.2
  have hM : 0≤M := hxy ▸ abs_nonneg _
  have hflip : (x,-y)∈A := by
    refine ⟨?_,?_⟩
    · simpa [K,Metric.mem_sphere,dist_zero_right,norm_neg] using And.intro hx hy
    · change |T.form x x (-y)|=M
      simpa only [map_neg,abs_neg] using hxy
  have hpos : 0≤ inner ℝ x y := by
    have h := hmax (a := (x,-y)) hflip
    change inner ℝ x (-y)≤ inner ℝ x y at h
    rw [inner_neg_right] at h
    linarith
  have hle : inner ℝ x y≤1 := by simpa only [hx,hy,mul_one] using real_inner_le_norm x y
  have heq : inner ℝ x y=1 := by
    by_contra hne
    have hlt : inner ℝ x y<1 := lt_of_le_of_ne hle hne
    have hn : ‖x+y‖^2=2+2*inner ℝ x y := by rw [norm_add_sq_real,hx,hy];ring
    have hnpos : 0<‖x+y‖ := by nlinarith [norm_nonneg (x+y)]
    have hnorm : ‖x+y‖≤2 := by simpa only [hx,hy,show (1:ℝ)+1=2 by norm_num] using norm_add_le x y
    have hsum : ‖x+y‖^2+‖x-y‖^2=4 := by
      rw [norm_add_sq_real,norm_sub_sq_real,hx,hy]
      ring
    have hplus := repeated_homogeneous_bound T M hbound (x+y) x hx
    have hminus := repeated_homogeneous_bound T M hbound (x-y) x hx
    have hpol : T.form (x+y) (x+y) x-T.form (x-y) (x-y) x=4*T.form x x y := by
      rw [cubic_polarization,T.swap₂ x y x]
    have hplus_eq : |T.form (x+y) (x+y) x|=M*‖x+y‖^2 := by
      rcases eq_or_eq_neg_of_abs_eq hxy with ht | ht
      · have hp := (abs_le.mp hplus).2
        have hm := (abs_le.mp hminus).1
        have he : T.form (x+y) (x+y) x=M*‖x+y‖^2 := by nlinarith
        rw [he,abs_of_nonneg (mul_nonneg hM (sq_nonneg _))]
      · have hp := (abs_le.mp hplus).1
        have hm := (abs_le.mp hminus).2
        have he : T.form (x+y) (x+y) x=-(M*‖x+y‖^2) := by nlinarith
        rw [he,abs_neg,abs_of_nonneg (mul_nonneg hM (sq_nonneg _))]
    let z := normalize (x+y)
    have hz : ‖z‖=1 := norm_normalize (norm_pos_iff.mp hnpos)
    have hzM : |T.form z z x|=M := by
      have he : T.form (x+y) (x+y) x=‖x+y‖^2*T.form z z x := by
        conv_lhs => rw [← norm_smul_normalize (x+y)]
        simp only [map_smul,smul_apply,smul_eq_mul]
        ring
      rw [he,abs_mul,abs_of_nonneg (sq_nonneg _)] at hplus_eq
      nlinarith [sq_pos_of_pos hnpos]
    have hzA : (z,x)∈A := by
      refine ⟨?_,hzM⟩
      simpa [K,Metric.mem_sphere,dist_zero_right] using And.intro hz hx
    have halign := hmax (a := (z,x)) hzA
    change inner ℝ z x≤ inner ℝ x y at halign
    have hzx : inner ℝ z x=‖x+y‖⁻¹*(1+inner ℝ x y) := by
      dsimp only [z,NormedSpace.normalize]
      rw [inner_smul_left,inner_add_left,real_inner_self_eq_norm_sq,hx,real_inner_comm y x]
      simp only [one_pow,conj_trivial]
    rw [hzx] at halign
    have hmult := mul_le_mul_of_nonneg_left halign hnpos.le
    have hc : ‖x+y‖*(‖x+y‖⁻¹*(1+inner ℝ x y))=1+inner ℝ x y := by
      field_simp
    rw [hc] at hmult
    have habound := mul_le_mul_of_nonneg_right hnorm hpos
    nlinarith
  have hsub : ‖x-y‖=0 := by
    have h := norm_sub_sq_real x y
    rw [hx,hy,heq] at h
    nlinarith [norm_nonneg (x-y)]
  have hxyEq : x=y := sub_eq_zero.mp (norm_eq_zero.mp hsub)
  exact ⟨x,hx,by simpa only [← hxyEq] using hxy⟩

/-- Banach's diagonal-to-mixed bound for genuine symmetric cubic tensors on
finite dimensional real Hilbert spaces.
Article: main_krylov, thm:Hp and apD:lem-binary(a).
Proof: compactness supplies a repeated-slot maximum, the alignment argument
makes it diagonal, and polarization bounds arbitrary mixed unit vectors. -/
theorem cubic_diagonal_bound_mixed [FiniteDimensional ℝ E]
    (T : SymmetricCubic E) (C : ℝ)
    (hdiag : ∀ x : E, ‖x‖=1 → |T.form x x x|≤C)
    (x y z : E) (hx : ‖x‖=1) (hy : ‖y‖=1) (hz : ‖z‖=1) :
    |T.form x y z|≤C := by
  have : Nontrivial E := nontrivial_of_ne x 0 (by
    intro h
    simp [h] at hx)
  obtain ⟨u,v,hu,hv,hmax⟩ := exists_repeated_max T
  let M := |T.form u u v|
  have hM : 0≤M := abs_nonneg _
  obtain ⟨w,hw,hwM⟩ := exists_diagonal_max_of_repeated T M hmax ⟨u,v,hu,hv,rfl⟩
  have hMC : M≤C := hwM ▸ hdiag w hw
  have hp := repeated_homogeneous_bound T M hmax (x+y) z hz
  have hm := repeated_homogeneous_bound T M hmax (x-y) z hz
  have hsum : ‖x+y‖^2+‖x-y‖^2=4 := by
    rw [norm_add_sq_real,norm_sub_sq_real,hx,hy]
    ring
  have hdiff := abs_sub (T.form (x+y) (x+y) z) (T.form (x-y) (x-y) z)
  rw [cubic_polarization,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)] at hdiff
  have hmix : |T.form x y z|≤M := by nlinarith
  exact hmix.trans hMC

/-- The unit diagonal estimate controls all vectors with their exact product
of Hilbert norms, including all zero-vector cases.
Article: main_krylov, thm:Hp and thm:Fexact, Banach's cubic identity. -/
theorem cubic_diagonal_bound [FiniteDimensional ℝ E]
    (T : SymmetricCubic E) (C : ℝ)
    (hdiag : ∀ x : E, ‖x‖=1 → |T.form x x x|≤C)
    (x y z : E) : |T.form x y z|≤C*‖x‖*‖y‖*‖z‖ := by
  by_cases hx : x=0
  · simp [hx]
  by_cases hy : y=0
  · simp [hy]
  by_cases hz : z=0
  · simp [hz]
  have hb := cubic_diagonal_bound_mixed T C hdiag
    (normalize x) (normalize y) (normalize z) (norm_normalize hx) (norm_normalize hy) (norm_normalize hz)
  have he : T.form x y z=(‖x‖*‖y‖*‖z‖)*T.form (normalize x) (normalize y) (normalize z) := by
    conv_lhs => rw [← norm_smul_normalize x,← norm_smul_normalize y,← norm_smul_normalize z]
    simp only [map_smul,smul_apply,smul_eq_mul]
    ring
  rw [he,abs_mul,abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : 0≤‖x‖*‖y‖*‖z‖)]

end
end krylov.Tensor
