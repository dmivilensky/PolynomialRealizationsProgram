import polyak.Numerics.Parametric.Invertible

/-!
Article: Appendix B, enclosure-independent parametric Krawczyk theorem.
Use: any proved interval evaluation backend supplies the actual Jacobian and
Newton-center enclosures. The norm defect itself proves nonsingularity of the
preconditioner, so no determinant computation is needed by the finite checker.
-/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine
open scoped Matrix.Norms.Operator

def enclosedImage {n : ℕ} (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) (J : Matrix (Fin n) (Fin n) IntervalRat)
    (C : Fin n → IntervalRat) : Fin n → IntervalRat :=
  fun i => IntervalRat.add (C i)
    (symmetricInterval (intervalMatrixBound (preconditionedJacobian Y J)*boxRadius X m))

def enclosureCheck {n : ℕ} (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) (J : Matrix (Fin n) (Fin n) IntervalRat)
    (C : Fin n → IntervalRat) : Bool :=
  decide (centerInside X m) &&
  decide (intervalMatrixBound (preconditionedJacobian Y J)<1) &&
  decide (∀ i, intervalStrictInside (enclosedImage X m Y J C i) (X i)=true)

def weightedEnclosureCheck {n : ℕ} (cert : WeightedCertificate n)
    (J : Matrix (Fin n) (Fin n) IntervalRat) (C : Fin n → IntervalRat) : Bool :=
  decide (∀ i, 0<cert.radius i) &&
    enclosureCheck (unitBox n) (normalized cert).center (normalized cert).preconditioner J C

noncomputable section

theorem fderiv_norm_le_of_enclosure {n : ℕ} (F : Fin n → Expr)
    (hF : ∀ i, ADSupported (F i)) (Y : Matrix (Fin n) (Fin n) ℚ)
    (J : Matrix (Fin n) (Fin n) IntervalRat) (s : ℝ) (x : Fin n → ℝ)
    (hJ : ∀ i j, jacobian F s x i j∈J i j) :
    ‖fderiv ℝ (newton (Y.map fun q => (q : ℝ)) F s) x‖≤
      (intervalMatrixBound (preconditionedJacobian Y J) : ℝ) := by
  rw [← Matrix.linfty_opNorm_toMatrix,newton_fderiv_matrix _ F hF]
  exact matrix_norm_le_intervalMatrixBound _ _ (mem_preconditionedJacobian Y _ J hJ)

theorem preconditioner_injective_of_enclosure {n : ℕ} (F : Fin n → Expr)
    (hF : ∀ i, ADSupported (F i)) (Y : Matrix (Fin n) (Fin n) ℚ)
    (J : Matrix (Fin n) (Fin n) IntervalRat) (s : ℝ) (x : Fin n → ℝ)
    (hJ : ∀ i j, jacobian F s x i j∈J i j)
    (hq : intervalMatrixBound (preconditionedJacobian Y J)<1) :
    Function.Injective (matrixCLM (Y.map fun q => (q : ℝ))) := by
  let R := matrixCLM (Y.map fun q => (q : ℝ))
  let D := fderiv ℝ (system F s) x
  have hn : ‖ContinuousLinearMap.id ℝ (Fin n → ℝ)-R.comp D‖<1 := by
    rw [← newton_fderiv _ F hF]
    exact (fderiv_norm_le_of_enclosure F hF Y J s x hJ).trans_lt (by exact_mod_cast hq)
  have hp : (R.comp D).IsInvertible :=
    isInvertible_of_defect (ContinuousLinearMap.id ℝ _) (R.comp D) (by simpa using hn)
  have hs : Function.Surjective R := by
    intro b
    obtain ⟨v,hv⟩ := hp.bijective.2 b
    exact ⟨D v,hv⟩
  exact (LinearMap.injective_iff_surjective (f := R.toLinearMap)).mpr hs

theorem fixedPoint_iff_zero_injective {n : ℕ} (F : Fin n → Expr)
    (Y : Matrix (Fin n) (Fin n) ℚ)
    (hinj : Function.Injective (matrixCLM (Y.map fun q => (q : ℝ))))
    (s : ℝ) (x : Fin n → ℝ) : newton (Y.map fun q => (q : ℝ)) F s x=x ↔ system F s x=0 := by
  constructor
  · intro hfix
    apply hinj
    have hm := congrArg (fun y => x-y) hfix
    change (Y.map fun q => (q : ℝ)).mulVec (system F s x)=
      (Y.map fun q => (q : ℝ)).mulVec 0
    simpa [newton] using hm
  · intro hz
    simp [newton,hz]

theorem newton_mem_enclosedImage {n : ℕ} (F : Fin n → Expr)
    (hF : ∀ i, ADSupported (F i)) (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun i => (m i : ℝ)) X) (Y : Matrix (Fin n) (Fin n) ℚ)
    (J : Matrix (Fin n) (Fin n) IntervalRat) (C : Fin n → IntervalRat) (s : ℝ)
    (hJ : ∀ x, FinBoxMem x X → ∀ i j, jacobian F s x i j∈J i j)
    (hC : ∀ i, newton (Y.map fun q => (q : ℝ)) F s (fun j => (m j : ℝ)) i∈C i)
    {x : Fin n → ℝ} (hx : FinBoxMem x X) (i : Fin n) :
    newton (Y.map fun q => (q : ℝ)) F s x i∈enclosedImage X m Y J C i := by
  let q := intervalMatrixBound (preconditionedJacobian Y J)
  let mr : Fin n → ℝ := fun j => (m j : ℝ)
  have hq0 : 0≤q := matrixBound_nonneg _
  have hd : ‖newton (Y.map fun q => (q : ℝ)) F s x-
      newton (Y.map fun q => (q : ℝ)) F s mr‖≤(q : ℝ)*‖x-mr‖ := by
    apply (finBoxSet_convex X).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    · exact fun _ _ => (newton_differentiable _ F hF s).differentiableAt
    · exact fun z hz => fderiv_norm_le_of_enclosure F hF Y J s z (hJ z hz)
    · exact hm
    · exact hx
  have hb : ‖newton (Y.map fun q => (q : ℝ)) F s x-
      newton (Y.map fun q => (q : ℝ)) F s mr‖≤((q*boxRadius X m : ℚ) : ℝ) := by
    calc
      _≤(q : ℝ)*‖x-mr‖ := hd
      _≤(q : ℝ)*(boxRadius X m : ℝ) := mul_le_mul_of_nonneg_left
        (norm_sub_center_le_boxRadius hx) (by exact_mod_cast hq0)
      _=_ := by push_cast; rfl
  have hc : |(newton (Y.map fun q => (q : ℝ)) F s x-
      newton (Y.map fun q => (q : ℝ)) F s mr) i|≤((q*boxRadius X m : ℚ) : ℝ) :=
    (norm_le_pi_norm _ i).trans hb
  have he : (newton (Y.map fun q => (q : ℝ)) F s x-
      newton (Y.map fun q => (q : ℝ)) F s mr) i∈symmetricInterval (q*boxRadius X m) := by
    rw [abs_le] at hc
    simpa [symmetricInterval,IntervalRat.mem_def,
      abs_of_nonneg (mul_nonneg hq0 (boxRadius_nonneg X m))] using hc
  simpa [enclosedImage,q,mr,Pi.sub_apply] using IntervalRat.mem_add (hC i) he

theorem enclosureCheck_sound {n : ℕ} (F : Fin n → Expr)
    (hF : ∀ i, ADSupported (F i)) (I : IntervalRat) (X : Fin n → IntervalRat)
    (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ)
    (J : Matrix (Fin n) (Fin n) IntervalRat) (C : Fin n → IntervalRat)
    (hJ : ∀ s∈I, ∀ x, FinBoxMem x X → ∀ i j, jacobian F s x i j∈J i j)
    (hC : ∀ s∈I, ∀ i, newton (Y.map fun q => (q : ℝ)) F s (fun j => (m j : ℝ)) i∈C i)
    (hc : enclosureCheck X m Y J C=true) :
    ∀ s∈I, ∃! x, FinBoxMem x X ∧ system F s x=0 := by
  simp only [enclosureCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨hm,hq⟩,hi⟩ := hc
  have hm' := centerInside_sound hm
  intro s hs
  have hinj := preconditioner_injective_of_enclosure F hF Y J s _ (hJ s hs _ hm') hq
  have hmap : Set.MapsTo (newton (Y.map fun q => (q : ℝ)) F s) (finBoxSet X) (finBoxSet X) := by
    intro x hx i
    exact intervalStrictInside_sound (hi i) _
      (newton_mem_enclosedImage F hF X m hm' Y J C s (hJ s hs) (hC s hs) hx i)
  obtain ⟨x,hx,huniq⟩ := contraction_unique_fixedPoint_in_finBox X _ hm'
    (newton (Y.map fun q => (q : ℝ)) F s) hmap
    (intervalMatrixBound (preconditionedJacobian Y J) : ℝ)
    (by exact_mod_cast matrixBound_nonneg (preconditionedJacobian Y J))
    (by exact_mod_cast hq) (fun _ _ => (newton_differentiable _ F hF s).differentiableAt)
    (fun z hz => fderiv_norm_le_of_enclosure F hF Y J s z (hJ s hs z hz))
  refine ⟨x,⟨hx.1,(fixedPoint_iff_zero_injective F Y hinj s x).mp hx.2⟩,?_⟩
  intro y hy
  exact huniq y ⟨hy.1,(fixedPoint_iff_zero_injective F Y hinj s y).mpr hy.2⟩

theorem weightedEnclosureCheck_sound {n : ℕ} (F : Fin n → Expr)
    (hF : ∀ i, ADSupported (F i)) (I : IntervalRat) (cert : WeightedCertificate n)
    (J : Matrix (Fin n) (Fin n) IntervalRat) (C : Fin n → IntervalRat)
    (hJ : ∀ s∈I, ∀ x, FinBoxMem x (unitBox n) → ∀ i j,
      jacobian (scaledSystem F cert.center cert.radius) s x i j∈J i j)
    (hC : ∀ s∈I, ∀ i, newton ((normalized cert).preconditioner.map fun q => (q : ℝ))
      (scaledSystem F cert.center cert.radius) s (fun j => ((normalized cert).center j : ℝ)) i∈C i)
    (hc : weightedEnclosureCheck cert J C=true) :
    ∀ s∈I, ∃! x, FinBoxMem x (coordinateBox cert.center cert.radius) ∧ system F s x=0 := by
  simp only [weightedEnclosureCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨hr,hcheck⟩ := hc
  intro s hs
  obtain ⟨y,hy,huniq⟩ := enclosureCheck_sound (scaledSystem F cert.center cert.radius)
    (fun j => substitute_supported _ (scaledVariable_supported cert.center cert.radius) _ (hF j))
    I (unitBox n) (normalized cert).center (normalized cert).preconditioner J C hJ hC hcheck s hs
  have hzero : system F s (chart cert.center cert.radius y)=0 := by
    rw [← scaledSystem_eval]
    exact hy.2
  refine ⟨chart cert.center cert.radius y,⟨chart_mem _ _ hr hy.1,hzero⟩,?_⟩
  intro x hx
  have he := chart_normalizePoint cert.center cert.radius hr x
  have hz : system (scaledSystem F cert.center cert.radius) s
      (normalizePoint cert.center cert.radius x)=0 := by
    rw [scaledSystem_eval,he]
    exact hx.2
  have hn := huniq _ ⟨normalizePoint_mem _ _ hr hx.1,hz⟩
  rw [← he,hn]

end
end polyak.Numerics.Parametric
