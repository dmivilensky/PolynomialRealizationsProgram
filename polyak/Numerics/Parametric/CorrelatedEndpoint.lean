import polyak.Numerics.Parametric.CorrelatedAnalytic
import polyak.Numerics.Parametric.Gluing

/-!
Article: Appendix B, exact compatibility at continuation slab endpoints.
Use: an endpoint Newton image transfers a true root from the left box to the
right box; the right box's proved uniqueness then identifies the branches.
-/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def correlatedEndpointImage {n : ℕ} (F : Fin n → Expr) (cert : WeightedCertificate n)
    (s : ℚ) (cfg : DyadicConfig) : Fin n → IntervalRat :=
  let I := IntervalRat.singleton s
  let J := memoMatrix (dyadicWeightedJacobian F I cert cfg)
  let C := memoFin (correlatedWeightedCenter F I cert cfg)
  fun i => IntervalRat.add (IntervalRat.singleton (cert.center i))
    (IntervalRat.scale (cert.radius i)
      (enclosedImage (unitBox n) (normalized cert).center (normalized cert).preconditioner J C i))

def checkCorrelatedEndpoint {n : ℕ} (F : Fin n → Expr)
    (left right : WeightedCertificate n) (s : ℚ) (cfg : DyadicConfig) : Bool :=
  decide (∀ i,(F i).checkADSupported=true) && decide (∀ i,0<left.radius i) &&
    dyadicJacobianSucceeded (scaledSystem F left.center left.radius)
      (IntervalRat.singleton s) (unitBox n) cfg &&
    dyadicResidualSucceeded (scaledSystem F left.center left.radius)
      (IntervalRat.singleton s) (normalized left).center cfg &&
    (let image := memoFin (correlatedEndpointImage F left s cfg)
     decide (∀ i,intervalSubset (image i) (coordinateBox right.center right.radius i)=true))

noncomputable section

theorem correlatedEndpointImage_mem {n : ℕ} (F : Fin n → Expr)
    (hF : ∀ i,ADSupported (F i)) (cert : WeightedCertificate n)
    (hr : ∀ i,0<cert.radius i) (s : ℚ) (cfg : DyadicConfig)
    (hJ : dyadicJacobianSucceeded (scaledSystem F cert.center cert.radius)
      (IntervalRat.singleton s) (unitBox n) cfg=true)
    (hC : dyadicResidualSucceeded (scaledSystem F cert.center cert.radius)
      (IntervalRat.singleton s) (normalized cert).center cfg=true)
    {x : Fin n → ℝ} (hx : FinBoxMem x (coordinateBox cert.center cert.radius))
    (hz : system F s x=0) (i : Fin n) : x i∈correlatedEndpointImage F cert s cfg i := by
  let Fs := scaledSystem F cert.center cert.radius
  have hFs : ∀ j,ADSupported (Fs j) := fun j =>
    substitute_supported _ (scaledVariable_supported cert.center cert.radius) _ (hF j)
  let y := normalizePoint cert.center cert.radius x
  have hy := normalizePoint_mem cert.center cert.radius hr hx
  have he := chart_normalizePoint cert.center cert.radius hr x
  have hz' : system Fs s y=0 := by
    rw [scaledSystem_eval,he]
    exact hz
  have hfix : newton ((normalized cert).preconditioner.map fun q => (q : ℝ)) Fs s y=y := by
    simp [newton,hz']
  have hm : FinBoxMem (fun j => ((normalized cert).center j : ℝ)) (unitBox n) := by
    intro j
    norm_num [normalized,unitBox,IntervalRat.mem_def]
  have hi := newton_mem_enclosedImage Fs hFs (unitBox n) (normalized cert).center hm
    (normalized cert).preconditioner (dyadicWeightedJacobian F (IntervalRat.singleton s) cert cfg)
    (correlatedWeightedCenter F (IntervalRat.singleton s) cert cfg) s
    (fun z hz i j => dyadicJacobian_mem Fs hFs (IntervalRat.singleton s) (unitBox n) cfg
      hJ (IntervalRat.mem_singleton s) hz i j)
    (fun i => correlatedCenterImage_mem Fs hFs (IntervalRat.singleton s) (normalized cert).center
      (normalized cert).preconditioner cfg hC (IntervalRat.mem_singleton s) i) hy i
  rw [hfix] at hi
  have hb := IntervalRat.mem_add (IntervalRat.mem_singleton (cert.center i))
    (IntervalRat.mem_scale (cert.radius i) hi)
  change chart cert.center cert.radius y i∈_ at hb
  rw [he] at hb
  simpa only [correlatedEndpointImage,memoMatrix_eq,memoFin_eq] using hb

theorem checkCorrelatedEndpoint_sound {n : ℕ} (F : Fin n → Expr)
    (left right : WeightedCertificate n) (s : ℚ) (cfg : DyadicConfig)
    (hc : checkCorrelatedEndpoint F left right s cfg=true)
    {x : Fin n → ℝ} (hx : FinBoxMem x (coordinateBox left.center left.radius))
    (hz : system F s x=0) : FinBoxMem x (coordinateBox right.center right.radius) := by
  simp only [checkCorrelatedEndpoint,memoFin_eq,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hF,hr⟩,hJ⟩,hC⟩,hi⟩ := hc
  have hF' : ∀ i,ADSupported (F i) := fun i => ((F i).checkADSupported_eq_true_iff).mp (hF i)
  exact fun i => intervalSubset_sound (hi i)
    (correlatedEndpointImage_mem F hF' left hr s cfg hJ hC hx hz i)

end
end polyak.Numerics.Parametric
