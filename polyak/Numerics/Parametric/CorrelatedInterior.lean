import polyak.Numerics.Parametric.CorrelatedEndpoint

/-! Article: Appendix B, checked roots lie in the open interiors of their boxes. -/
noncomputable section
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def strictBox {n : ℕ} (X : Fin n → IntervalRat) : Set (Fin n → ℝ) :=
  {x | ∀ i,(X i).lo<x i ∧ x i<(X i).hi}

theorem isOpen_strictBox {n : ℕ} (X : Fin n → IntervalRat) : IsOpen (strictBox X) := by
  unfold strictBox
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite (fun i =>
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const))

theorem strictBox_subset {n : ℕ} {X : Fin n → IntervalRat} {x : Fin n → ℝ}
    (hx : x∈strictBox X) : FinBoxMem x X := fun i => ⟨(hx i).1.le,(hx i).2.le⟩

theorem checkCorrelated_root_strict {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (cert : WeightedCertificate n) (cfg : DyadicConfig)
    (hc : checkCorrelated F I cert cfg=true) {s : ℝ} {x : Fin n → ℝ}
    (hs : s∈I) (hx : FinBoxMem x (coordinateBox cert.center cert.radius))
    (hz : system F s x=0) : x∈strictBox (coordinateBox cert.center cert.radius) := by
  have hd := hc
  simp only [checkCorrelated,memoMatrix_eq,memoFin_eq,Bool.and_eq_true,decide_eq_true_eq] at hd
  obtain ⟨⟨⟨hF,hJ⟩,hC⟩,hcheck⟩ := hd
  simp only [weightedEnclosureCheck,enclosureCheck,Bool.and_eq_true,decide_eq_true_eq] at hcheck
  obtain ⟨hr,⟨⟨hm,_⟩,hi⟩⟩ := hcheck
  let Fs := scaledSystem F cert.center cert.radius
  have hFs : ∀ i,ADSupported (Fs i) := fun i => substitute_supported _
    (scaledVariable_supported cert.center cert.radius) _
      (((F i).checkADSupported_eq_true_iff).mp (hF i))
  let y := normalizePoint cert.center cert.radius x
  have hy := normalizePoint_mem cert.center cert.radius hr hx
  have he := chart_normalizePoint cert.center cert.radius hr x
  have hz' : system Fs s y=0 := by
    rw [scaledSystem_eval,he]
    exact hz
  have hfix : newton ((normalized cert).preconditioner.map fun q => (q : ℝ)) Fs s y=y := by
    simp [newton,hz']
  have hb (i : Fin n) := newton_mem_enclosedImage Fs hFs (unitBox n) (normalized cert).center
    (centerInside_sound hm) (normalized cert).preconditioner (dyadicWeightedJacobian F I cert cfg)
    (correlatedWeightedCenter F I cert cfg) s
    (fun z hz i j => dyadicJacobian_mem Fs hFs I (unitBox n) cfg hJ hs hz i j)
    (fun i => correlatedCenterImage_mem Fs hFs I (normalized cert).center
      (normalized cert).preconditioner cfg hC hs i) hy i
  intro i
  have hb' := hb i
  rw [hfix] at hb'
  have hi' := hi i
  simp only [intervalStrictInside,Bool.and_eq_true,decide_eq_true_eq] at hi'
  have hlo : ((unitBox n i).lo : ℝ)<
      ((enclosedImage (unitBox n) (normalized cert).center (normalized cert).preconditioner
        (dyadicWeightedJacobian F I cert cfg) (correlatedWeightedCenter F I cert cfg) i).lo : ℝ) := by
    exact_mod_cast hi'.1
  have hhi : ((enclosedImage (unitBox n) (normalized cert).center (normalized cert).preconditioner
        (dyadicWeightedJacobian F I cert cfg) (correlatedWeightedCenter F I cert cfg) i).hi : ℝ)<
      ((unitBox n i).hi : ℝ) := by exact_mod_cast hi'.2
  have hl := hlo.trans_le hb'.1
  have hu := hb'.2.trans_lt hhi
  have hri : (0 : ℝ)<cert.radius i := by exact_mod_cast hr i
  have hex : x i=(cert.center i : ℝ)+(cert.radius i : ℝ)*y i := by
    simpa only [chart] using (congrFun he i).symm
  simp only [unitBox,Rat.cast_neg,Rat.cast_one] at hl hu
  change ((coordinateBox cert.center cert.radius i).lo : ℝ)<x i ∧
    x i<((coordinateBox cert.center cert.radius i).hi : ℝ)
  simp only [coordinateBox,IntervalRat.add,IntervalRat.singleton,
    symmetricInterval,abs_of_pos (hr i),Rat.cast_add,Rat.cast_neg]
  constructor <;> nlinarith

end polyak.Numerics.Parametric
