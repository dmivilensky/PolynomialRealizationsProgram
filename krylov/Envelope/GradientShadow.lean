import krylov.Envelope.GradientProjection
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), actual absorbed moving-shadow compression.
Use: compress true physical increments off the actual moving CG flag,
retain their genuine absorbed reference first jet and annihilate every
actual earlier shadow probe exactly.
Source: the true active CG-gradient projector, actual symmetric operator
pairings and standard continuous and smooth operator composition.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every true increment annihilating the actual old CG gradients also annihilates their genuine finite projection image.
Use: Every true increment annihilating the actual old CG gradients also annihilates their genuine finite projection image.
Article: main_krylov, apB:lem:mu(c), actual absorbed moving-shadow compression.
Proof: Expand the actual finite gradient-coordinate synthesis and apply the true zero increment action on each real generator. -/
theorem gradientProjection_annihilated (Q D : E →L[ℝ] E) (g : E) (k : ℕ)
    (hkill : ∀ i≤k, D (CG.gradient Q g i)=0) (v : E) : D (gradientProjection Q g k v)=0 := by
  -- Actual gradient-coordinate expansion reduces flag annihilation to the genuine increment action on each true reference gradient.
  rw [gradientProjection_apply]
  change D (∑ i∈Finset.range (k+1), (inner ℝ (CG.gradient Q g i) v/‖CG.gradient Q g i‖^2) • CG.gradient Q g i)=0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul,hkill i (by have := Finset.mem_range.mp hi;omega),smul_zero]

/-- The true old CG-gradient projection annihilates the image of every actual symmetric increment killing the genuine old gradient flag.
Use: The true old CG-gradient projection annihilates the image of every actual symmetric increment killing the genuine old gradient flag.
Article: main_krylov, apB:lem:mu(c), actual absorbed moving-shadow compression.
Proof: Move the real symmetric increment across each genuine inner product, whose true old-gradient image is zero. -/
theorem gradientProjection_annihilates_image (Q D : E →L[ℝ] E) (g : E) (k : ℕ)
    (hD : D.toLinearMap.IsSymmetric) (hkill : ∀ i≤k, D (CG.gradient Q g i)=0) (v : E) :
    gradientProjection Q g k (D v)=0 := by
  rw [gradientProjection_apply]
  change (∑ i∈Finset.range (k+1), (inner ℝ (CG.gradient Q g i) (D v)/‖CG.gradient Q g i‖^2) • CG.gradient Q g i)=0
  -- Genuine symmetry transfers the physical increment to its actual zero old-gradient image.
  apply Finset.sum_eq_zero
  intro i hi
  have he := hD (CG.gradient Q g i) v
  change inner ℝ (D (CG.gradient Q g i)) v=inner ℝ (CG.gradient Q g i) (D v) at he
  rw [← he,hkill i (by have := Finset.mem_range.mp hi;omega),inner_zero_left,zero_div,zero_smul]

/-- The actual symmetric physical increment compressed off the true moving CG-gradient flag.
Use: The actual symmetric physical increment compressed off the true moving CG-gradient flag.
Article: main_krylov, apB:lem:mu(c), actual absorbed moving-shadow compression.
Proof: Apply the genuine complementary gradient projection on both sides of the real increment. -/
def shadowCompression (Q D : E →L[ℝ] E) (g : E) (l : ℕ) : E →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ E-gradientProjection Q g l) ∘L D ∘L
    (ContinuousLinearMap.id ℝ E-gradientProjection Q g l)

/-- Compressing a genuine symmetric absorbed increment off the actual reference CG flag leaves it exactly unchanged.
Use: Compressing a genuine symmetric absorbed increment off the actual reference CG flag leaves it exactly unchanged.
Article: main_krylov, apB:lem:mu(c), actual absorbed moving-shadow compression.
Proof: The true increment annihilates the real projected flag and its actual image is orthogonal to that flag, so both genuine complementary factors act identically. -/
theorem shadowCompression_eq (Q D : E →L[ℝ] E) (g : E) (l : ℕ)
    (hD : D.toLinearMap.IsSymmetric) (hkill : ∀ i≤l, D (CG.gradient Q g i)=0) :
    shadowCompression Q D g l=D := by
  ext v
  change D (v-gradientProjection Q g l v)-gradientProjection Q g l (D (v-gradientProjection Q g l v))=D v
  rw [map_sub,gradientProjection_annihilated Q D g l hkill v,sub_zero,
    gradientProjection_annihilates_image Q D g l hD hkill v,sub_zero]

/-- Every actual moving shadow increment annihilates each true earlier computed CG direction exactly.
Use: Every actual moving shadow increment annihilates each true earlier computed CG direction exactly.
Article: main_krylov, apB:lem:mu(c), actual absorbed moving-shadow compression.
Proof: The genuine complementary projector kills that real direction before applying the actual increment. -/
theorem shadowCompression_direction (Q D : E →L[ℝ] E) (g : E) (l j : ℕ)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i≤l, CG.gradient Q g i≠0) (hj : j≤l) :
    shadowCompression Q D g l (CG.direction Q g j)=0 := by
  change (ContinuousLinearMap.id ℝ E-gradientProjection Q g l)
    (D (CG.direction Q g j-gradientProjection Q g l (CG.direction Q g j)))=0
  rw [gradientProjection_direction Q hQ hpos g l j hpre hj,sub_self,map_zero,map_zero]

/-- The true moving compressed increment is continuous in the actual operator norm on every genuine active reference-gradient chart.
Use: The true moving compressed increment is continuous in the actual operator norm on every genuine active reference-gradient chart.
Article: main_krylov, apB:lem:mu(c), actual absorbed moving-shadow compression.
Proof: Compose the real continuous complementary gradient projectors with the actual fixed increment. -/
theorem shadowCompression_continuousAt (Q : ℝ → E →L[ℝ] E) (D : E →L[ℝ] E) (g : E) (l : ℕ)
    (hG : ∀ i≤l, ContinuousAt (fun t => CG.gradient (Q t) g i) 0)
    (hpre : ∀ i≤l, CG.gradient (Q 0) g i≠0) :
    ContinuousAt (fun t => shadowCompression (Q t) D g l) 0 := by
  have hP := gradientProjection_continuousAt Q (fun _ => g) 0 l hG hpre
  exact ((continuousAt_const.sub hP).clm_comp continuousAt_const).clm_comp (continuousAt_const.sub hP)
/-- The true moving compressed increment inherits every genuine C-r regularity order of its actual active gradient chart.
Use: The true moving compressed increment inherits every genuine C-r regularity order of its actual active gradient chart.
Article: main_krylov, apB:lem:mu(c), actual absorbed moving-shadow compression.
Proof: Compose the proved actual C-r complementary gradient projections with the genuine fixed physical increment. -/
theorem shadowCompression_contDiffAt (Q : ℝ → E →L[ℝ] E) (D : E →L[ℝ] E) (g : E) (l : ℕ)
    (r : WithTop ℕ∞) (hG : ∀ i≤l, ContDiffAt ℝ r (fun t => CG.gradient (Q t) g i) 0)
    (hpre : ∀ i≤l, CG.gradient (Q 0) g i≠0) :
    ContDiffAt ℝ r (fun t => shadowCompression (Q t) D g l) 0 := by
  have hP := gradientProjection_contDiffAt Q (fun _ => g) 0 l r hG hpre
  exact ((contDiffAt_const.sub hP).clm_comp contDiffAt_const).clm_comp (contDiffAt_const.sub hP)

end
end krylov.Envelope
