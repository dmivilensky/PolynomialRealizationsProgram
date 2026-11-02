import krylov.Correction.SharpRestartProjection
import krylov.Correction.SharpRestartScalar

/-!
Article: main_krylov, apG:restart, genuine sharp restart energy estimate.
Use: derive the scalar restart quadratic from the actual observed old
span and measured conjugacy, retaining the true positive reference scale.
Source: orthogonal projection and Cauchy--Schwarz in the actual positive
square-root energy. The source short-step norm is kept canonical.
-/
namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- Positive-root energy is the actual physical quadratic pairing.
Article: main_krylov, apG:restart, B^2=b^T H b. -/
theorem restart_root_pairing (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ u (cgOperator H v)=
      inner ℝ (cgOperator (metricRoot H) u) (cgOperator (metricRoot H) v) := by
  rw [canonical_search_pairing H hH,canonical_reference_action H hH]
  rfl

/-- A genuine positive reference upper endpoint bounds its true positive
root, without losing a spectral scale. Article: apG:restart. -/
theorem restart_root_norm (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (m r : ℝ) (hm : 0<m) (hr : 0≤r) (hupper : ‖cgOperator H‖≤m^2*r^2) :
    ‖cgOperator (metricRoot H)‖≤m*r := by
  have hs : star (metricRoot H)=metricRoot H := by
    rw [star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial,(metricRoot_isSymm H).eq]
  have he : ‖metricRoot H‖^2=‖H‖ := by
    calc
      _ = ‖star (metricRoot H)*metricRoot H‖ := by rw [CStarRing.norm_star_mul_self,pow_two]
      _ = ‖H‖ := by rw [hs,metricRoot_square H hH]
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot H)‖≤m*r
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖≤_ at hupper
  rw [Matrix.l2_opNorm_toEuclideanCLM] at hupper
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hm.le hr)).mp
  rw [mul_pow,he]
  exact hupper

/-- The true old-span decomposition gives the normalized original energy
quadratic. Its only directional hypotheses are the actual span equation
and the measured small projected component, both derived from the real
observed inverse solve in the source wrapper. Article: apG:restart. -/
theorem restart_normalized_energy (s : Fin p → EuclideanSpace ℝ (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (g d : EuclideanSpace ℝ (Fin n)) (m r : ℝ) (hm : 0<m) (hr : 1≤r)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),m^2*‖v‖^2≤ inner ℝ v (cgOperator H v))
    (hupper : ‖cgOperator H‖≤m^2*r^2)
    (hspan : d+cgOperator H g∈Submodule.span ℝ (Set.range s))
    (hproj : 8*r^2*‖observedProjection s d‖≤‖d‖) :
    let a := observedProjection s g
    let b := g-a
    let z := ‖cgOperator (metricRoot H) b‖/m
    ‖g‖≤‖a‖+z ∧ ‖d‖≤2*m^2*r^2*‖g‖ ∧
      z^2≤(-inner ℝ g d)/m^2+(r+1/4)*‖a‖*z+‖a‖^2/4 := by
  let a := observedProjection s g
  let b := g-a
  let B := ‖cgOperator (metricRoot H) b‖
  let z := B/m
  have hr0 : 0≤r := by linarith
  have hr2 : 0<r^2 := by positivity
  have ha := (Submodule.span ℝ (Set.range s)).starProjection_apply_mem g
  have hb := (Submodule.span ℝ (Set.range s)).starProjection_inner_eq_zero g (d+cgOperator H g) hspan
  change inner ℝ b (d+cgOperator H g)=0 at hb
  rw [inner_add_right] at hb
  have hd := (Submodule.span ℝ (Set.range s)).starProjection_inner_eq_zero d a ha
  change inner ℝ (d-observedProjection s d) a=0 at hd
  rw [inner_sub_left] at hd
  have hdPair : inner ℝ a d=inner ℝ a (observedProjection s d) := by
    calc
      _ = inner ℝ d a := real_inner_comm _ _
      _ = inner ℝ (observedProjection s d) a := sub_eq_zero.mp hd
      _ = _ := real_inner_comm _ _
  have hB : B^2=inner ℝ b (cgOperator H b) := by
    rw [restart_root_pairing H hH,real_inner_self_eq_norm_sq]
  have hmb : m*‖b‖≤B := by
    have hl := hlower b
    rw [←hB] at hl
    nlinarith [norm_nonneg b,norm_nonneg (cgOperator (metricRoot H) b)]
  have hbz : ‖b‖≤z := (le_div_iff₀ hm).mpr (by nlinarith only [hmb])
  have hgz : ‖g‖≤‖a‖+z := by
    have he : g=a+b := by dsimp only [a,b]; abel
    exact (he ▸ norm_add_le a b).trans (add_le_add le_rfl hbz)
  have hp : ‖observedProjection s d‖≤(1/2 : ℝ)*‖d‖ := by
    nlinarith [norm_nonneg (observedProjection s d),sq_nonneg (r-1)]
  have hdn := projected_direction_sharp s (cgOperator H) g d hspan (by norm_num : (1/2 : ℝ)≤1/2) hp
  have hdN : ‖d‖≤2*m^2*r^2*‖g‖ := hdn.trans (by
    nlinarith [mul_le_mul_of_nonneg_right hupper (norm_nonneg g)])
  have hpN : ‖observedProjection s d‖≤m^2/4*‖g‖ := by
    nlinarith [hproj.trans hdN]
  have hroot := restart_root_norm H hH m r hm hr0 hupper
  have hcross : -inner ℝ b (cgOperator H a)≤B*(m*r*‖a‖) := by
    rw [restart_root_pairing H hH]
    have hi := norm_inner_le_norm (𝕜 := ℝ) (cgOperator (metricRoot H) b) (cgOperator (metricRoot H) a)
    rw [Real.norm_eq_abs] at hi
    have hn := (cgOperator (metricRoot H)).le_opNorm a
    have hna := hn.trans (mul_le_mul_of_nonneg_right hroot (norm_nonneg a))
    exact (neg_le_abs _).trans (hi.trans (mul_le_mul_of_nonneg_left hna (norm_nonneg _)))
  have hproject : inner ℝ a (observedProjection s d)≤m^2/4*‖a‖*(‖a‖+z) := by
    have hh := mul_le_mul_of_nonneg_left hpN (norm_nonneg a)
    have hgg := mul_le_mul_of_nonneg_left hgz (by positivity : 0≤m^2/4*‖a‖)
    calc
      _ ≤ ‖a‖*‖observedProjection s d‖ := real_inner_le_norm _ _
      _ ≤ ‖a‖*(m^2/4*‖g‖) := hh
      _ = m^2/4*‖a‖*‖g‖ := by ring
      _ ≤ _ := hgg
  have hident : inner ℝ b (cgOperator H b)= -inner ℝ g d-inner ℝ b (cgOperator H a)+
      inner ℝ a (observedProjection s d) := by
    have he : g=b+a := by dsimp only [a,b]; abel
    rw [he,map_add,inner_add_right] at hb
    have hg := congrArg (fun v=>inner ℝ v d) he
    rw [inner_add_left] at hg
    linarith only [hb,hg,hdPair]
  refine ⟨hgz,hdN,?_⟩
  have he : B=m*z := by dsimp only [z]; field_simp
  have henergy : B^2≤-inner ℝ g d+B*(m*r*‖a‖)+m^2/4*‖a‖*(‖a‖+z) := by
    rw [hB,hident]
    linarith
  have hdiv : m^2*z^2≤-inner ℝ g d+m^2*((r+1/4)*‖a‖*z+‖a‖^2/4) := by
    rw [he] at henergy
    nlinarith only [henergy]
  calc
    z^2 ≤ (-inner ℝ g d+m^2*((r+1/4)*‖a‖*z+‖a‖^2/4))/m^2 :=
      (le_div_iff₀ (sq_pos_of_pos hm)).mpr (by nlinarith only [hdiv])
    _ = (-inner ℝ g d)/m^2+(r+1/4)*‖a‖*z+‖a‖^2/4 := by field_simp; ring

end
end krylov.Correction
