import polyak.Numerics.Parametric.Weighted

/-!
Article: Appendix B, separate root inclusions at common slab endpoints.
Use: a fresh Newton image at the exact endpoint puts the left root in the
right box. Uniqueness of the checked right box then identifies the two roots.
-/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def intervalSubset (I J : IntervalRat) : Bool := decide (J.lo≤I.lo ∧ I.hi≤J.hi)

def endpointImage {n : ℕ} (F : Fin n → Expr) (cert : WeightedCertificate n)
    (s : ℚ) (cfg : EvalConfig := {}) : Fin n → IntervalRat :=
  fun i => IntervalRat.add (IntervalRat.singleton (cert.center i))
    (IntervalRat.scale (cert.radius i)
      (image (scaledSystem F cert.center cert.radius) (IntervalRat.singleton s) (unitBox n)
        (normalized cert).center (normalized cert).preconditioner cfg i))

def checkEndpoint {n : ℕ} (F : Fin n → Expr) (left right : WeightedCertificate n)
    (s : ℚ) (cfg : EvalConfig := {}) : Bool :=
  decide (∀ i, intervalSubset (endpointImage F left s cfg i)
    (coordinateBox right.center right.radius i)=true)

noncomputable section

theorem intervalSubset_sound {I J : IntervalRat} (h : intervalSubset I J=true)
    {x : ℝ} (hx : x∈I) : x∈J := by
  simp only [intervalSubset,decide_eq_true_eq] at h
  have hlo : (J.lo : ℝ)≤I.lo := by exact_mod_cast h.1
  have hhi : (I.hi : ℝ)≤J.hi := by exact_mod_cast h.2
  exact ⟨hlo.trans hx.1,hx.2.trans hhi⟩

theorem endpointImage_mem {n : ℕ} (F : Fin n → Expr) (hF : ∀ i, ADSupported (F i))
    (cert : WeightedCertificate n) (hr : ∀ i, 0<cert.radius i) (s : ℚ)
    {x : Fin n → ℝ} (hx : FinBoxMem x (coordinateBox cert.center cert.radius))
    (hz : system F s x=0) (cfg : EvalConfig) (i : Fin n) : x i∈endpointImage F cert s cfg i := by
  let y := normalizePoint cert.center cert.radius x
  have hy := normalizePoint_mem cert.center cert.radius hr hx
  have he := chart_normalizePoint cert.center cert.radius hr x
  have hz' : system (scaledSystem F cert.center cert.radius) s y=0 := by
    rw [scaledSystem_eval,he]
    exact hz
  have hfix : newton ((normalized cert).preconditioner.map fun q => (q : ℝ))
      (scaledSystem F cert.center cert.radius) s y=y := by simp [newton,hz']
  have hm : FinBoxMem (fun j => ((normalized cert).center j : ℝ)) (unitBox n) := by
    intro j
    norm_num [normalized,unitBox,IntervalRat.mem_def]
  have himage := newton_mem_image (scaledSystem F cert.center cert.radius)
    (fun j => substitute_supported _ (scaledVariable_supported cert.center cert.radius) _ (hF j))
    (IntervalRat.singleton s) (unitBox n) (normalized cert).center hm
    (normalized cert).preconditioner cfg (IntervalRat.mem_singleton s) hy i
  rw [hfix] at himage
  have hbound := IntervalRat.mem_add (IntervalRat.mem_singleton (cert.center i))
    (IntervalRat.mem_scale (cert.radius i) himage)
  change chart cert.center cert.radius y i∈endpointImage F cert s cfg i at hbound
  rwa [he] at hbound

theorem checkEndpoint_sound {n : ℕ} (F : Fin n → Expr) (hF : ∀ i, ADSupported (F i))
    (left right : WeightedCertificate n) (hr : ∀ i, 0<left.radius i) (s : ℚ)
    (cfg : EvalConfig) (hc : checkEndpoint F left right s cfg=true)
    {x : Fin n → ℝ} (hx : FinBoxMem x (coordinateBox left.center left.radius))
    (hz : system F s x=0) : FinBoxMem x (coordinateBox right.center right.radius) := by
  simp only [checkEndpoint,decide_eq_true_eq] at hc
  exact fun i => intervalSubset_sound (hc i) (endpointImage_mem F hF left hr s hx hz cfg i)

def selected {n : ℕ} (F : Fin n → Expr) (I : IntervalRat) (cert : WeightedCertificate n)
    (cfg : EvalConfig) (hc : checkWeighted F I cert cfg=true) (s : ℝ) : Fin n → ℝ := by
  classical
  exact if hs : s∈I then (checkWeighted_sound F I cert cfg hc s hs).choose
    else fun i => (cert.center i : ℝ)

theorem selected_spec {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (cert : WeightedCertificate n) (cfg : EvalConfig) (hc : checkWeighted F I cert cfg=true)
    {s : ℝ} (hs : s∈I) :
    FinBoxMem (selected F I cert cfg hc s) (coordinateBox cert.center cert.radius) ∧
      system F s (selected F I cert cfg hc s)=0 := by
  classical
  simpa only [selected,dite_eq_left hs] using (checkWeighted_sound F I cert cfg hc s hs).choose_spec.1

theorem selected_unique {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (cert : WeightedCertificate n) (cfg : EvalConfig) (hc : checkWeighted F I cert cfg=true)
    {s : ℝ} (hs : s∈I) {x : Fin n → ℝ}
    (hx : FinBoxMem x (coordinateBox cert.center cert.radius)) (hz : system F s x=0) :
    x=selected F I cert cfg hc s := by
  exact (checkWeighted_sound F I cert cfg hc s hs).unique ⟨hx,hz⟩
    (selected_spec F I cert cfg hc hs)

theorem endpoint_roots_eq {n : ℕ} (F : Fin n → Expr) (hF : ∀ i, ADSupported (F i))
    (Il Ir : IntervalRat) (left right : WeightedCertificate n) (s : ℚ) (cfg : EvalConfig)
    (hl : checkWeighted F Il left cfg=true) (hr : checkWeighted F Ir right cfg=true)
    (hpoint : (s : ℝ)∈Ir) (he : checkEndpoint F left right s cfg=true)
    {x y : Fin n → ℝ} (hx : FinBoxMem x (coordinateBox left.center left.radius))
    (hz : system F s x=0) (hy : FinBoxMem y (coordinateBox right.center right.radius))
    (hw : system F s y=0) : x=y := by
  have hrad : ∀ i, 0<left.radius i := by
    have hh := hl
    simp only [checkWeighted,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.1
  exact (checkWeighted_sound F Ir right cfg hr s hpoint).unique
    ⟨checkEndpoint_sound F hF left right hrad s cfg he hx hz,hz⟩ ⟨hy,hw⟩

end
end polyak.Numerics.Parametric
