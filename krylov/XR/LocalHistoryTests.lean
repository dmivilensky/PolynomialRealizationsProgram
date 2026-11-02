import krylov.XR.LocalHistoryDictionary
import krylov.XR.LocalPositive
import krylov.XR.MemoryRank
import krylov.XR.XRFCReplay

/-!
Article: main_krylov, lem:xr-local, actual finite model-test stability.
Use: genuine endpoint-coordinate regularity and strict reference data
force actual independence, Hermitian tests and scalar oversized-term
gates nearby. No successful test of a perturbed execution is assumed.
Source: openness of finite independence and the proved actual Hermitian
Cholesky domain, together with elementary strict scalar continuity.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant Filter Topology
open scoped InnerProductSpace ComplexOrder
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual ordinary or F Hermitian test in true endpoint coordinates. -/
def endpointHermitianTest {k : ℕ} (theta : ℝ) (values : Bool) (C : EndpointChart E k) :
    Matrix (Fin k) (Fin k) ℂ :=
  (endpointVirtualModel values C).map Complex.ofReal +
    (Complex.I / (theta : ℂ)) • (defect (crossGram (endpointStep C) (endpointImage C))).map Complex.ofReal

/-- The complex matrix computed from true endpoints is always Hermitian,
including the value-corrected diagonal and a totalized zero threshold. -/
theorem endpointHermitianTest_isHermitian {k : ℕ} (theta : ℝ) (values : Bool)
    (C : EndpointChart E k) : (endpointHermitianTest theta values C).IsHermitian := by
  have hT : (endpointVirtualModel values C).IsSymm := by
    unfold endpointVirtualModel Matrix.IsSymm
    rw [transpose_sub, (latest_isSymm _).eq, diagonal_transpose]
  apply (ofReal_isHermitian _ hT).add
  ext i j
  have hd := congrFun (congrFun (defect_transpose (crossGram (endpointStep C) (endpointImage C))) i) j
  change defect (crossGram (endpointStep C) (endpointImage C)) j i =
    -defect (crossGram (endpointStep C) (endpointImage C)) i j at hd
  change star ((Complex.I / (theta : ℂ)) * Complex.ofReal
    (defect (crossGram (endpointStep C) (endpointImage C)) j i)) =
    (Complex.I / (theta : ℂ)) * Complex.ofReal
      (defect (crossGram (endpointStep C) (endpointImage C)) i j)
  rw [hd, Complex.ofReal_neg]
  simp
  ring

/-- The genuine scalar and complex window tests are continuous functions
of actual smooth endpoints on their real secant-quotient domain. -/
theorem continuousAt_endpointHermitianTest {k : ℕ}
    (theta : ℝ) (values : Bool) (C : X → EndpointChart E k) (x : X)
    (hC : ContDiffAt ℝ 2 C x)
    (hq : ∀ i, inner ℝ (endpointStep (C x) i) (endpointImage (C x) i) ≠ 0) :
    ContinuousAt (fun z => endpointHermitianTest theta values (C z)) x := by
  have hs (i : Fin k) : ContinuousAt (fun z => endpointStep (C z) i) x :=
    ((continuousAt_pi.mp hC.continuousAt.fst) i.succ).sub
      ((continuousAt_pi.mp hC.continuousAt.fst) i.castSucc)
  have hy (i : Fin k) : ContinuousAt (fun z => endpointImage (C z) i) x :=
    ((continuousAt_pi.mp hC.continuousAt.snd.snd) i.succ).sub
      ((continuousAt_pi.mp hC.continuousAt.snd.snd) i.castSucc)
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  have hm := (contDiff_endpointVirtualModel values C x hC hq i j).continuousAt
  have hd : ContinuousAt (fun z => inner ℝ (endpointStep (C z) i) (endpointImage (C z) j) -
      inner ℝ (endpointStep (C z) j) (endpointImage (C z) i)) x :=
    ((hs i).inner (hy j)).sub ((hs j).inner (hy i))
  exact (Complex.continuous_ofReal.continuousAt.comp hm).add
    (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hd))

/-- Genuine strict reference model decisions persist near the actual
reference endpoint data. Both ordinary and F complex test success and all
oversized-term gates are conclusions of continuity. -/
theorem endpoint_model_tests_eventually {k : ℕ}
    (theta : ℝ) (C : X → EndpointChart E k) (x : X) (hC : ContDiffAt ℝ 2 C x)
    (hq : ∀ i, inner ℝ (endpointStep (C x) i) (endpointImage (C x) i) ≠ 0)
    (hLI : LinearIndependent ℝ (endpointStep (C x)))
    (hordinary : (endpointHermitianTest theta false (C x)).PosDef)
    (hcorrected : (endpointHermitianTest theta true (C x)).PosDef)
    (hoversize : ∀ i,
      |12 * endpointSplit (C x) i * endpointDefect (C x) i| <
        inner ℝ (endpointStep (C x) i) (endpointImage (C x) i) / 2) :
    ∀ᶠ z in 𝓝 x,
      LinearIndependent ℝ (endpointStep (C z)) ∧
      (endpointHermitianTest theta false (C z)).PosDef ∧
      (endpointHermitianTest theta true (C z)).PosDef ∧
      ∀ i, |12 * endpointSplit (C z) i * endpointDefect (C z) i| <
        inner ℝ (endpointStep (C z) i) (endpointImage (C z) i) / 2 := by
  have hs (i : Fin k) : ContDiffAt ℝ 2 (fun z => endpointStep (C z) i) x :=
    ((contDiffAt_pi.mp hC.fst) i.succ).sub ((contDiffAt_pi.mp hC.fst) i.castSucc)
  have hy (i : Fin k) : ContDiffAt ℝ 2 (fun z => endpointImage (C z) i) x :=
    ((contDiffAt_pi.mp hC.snd.snd) i.succ).sub ((contDiffAt_pi.mp hC.snd.snd) i.castSucc)
  have hli := (contDiffAt_pi.mpr hs).continuousAt.tendsto.eventually hLI.eventually
  have hord := eventually_posDef_of_continuousAt_hermitian _ x
    (continuousAt_endpointHermitianTest theta false C x hC hq)
    (Filter.Eventually.of_forall (fun z => endpointHermitianTest_isHermitian theta false (C z))) hordinary
  have hcor := eventually_posDef_of_continuousAt_hermitian _ x
    (continuousAt_endpointHermitianTest theta true C x hC hq)
    (Filter.Eventually.of_forall (fun z => endpointHermitianTest_isHermitian theta true (C z))) hcorrected
  have hscalar (i : Fin k) : ∀ᶠ z in 𝓝 x,
      |12 * endpointSplit (C z) i * endpointDefect (C z) i| <
        inner ℝ (endpointStep (C z) i) (endpointImage (C z) i) / 2 := by
    have hm₀ := contDiff_endpointVirtualModel false C x hC hq i i
    have hm₁ := contDiff_endpointVirtualModel true C x hC hq i i
    have he (z : X) : 12 * endpointSplit (C z) i * endpointDefect (C z) i =
        endpointVirtualModel false (C z) i i - endpointVirtualModel true (C z) i i := by
      simp only [endpointVirtualModel, Bool.false_eq_true, ite_false, ite_true,
        Matrix.sub_apply, diagonal_apply_eq]
      ring
    have hleft : ContinuousAt (fun z => |12 * endpointSplit (C z) i * endpointDefect (C z) i|) x := by
      simp_rw [he]
      exact (hm₀.sub hm₁).continuousAt.abs
    have hright := (((hs i).inner ℝ (hy i)).div_const 2).continuousAt
    exact (hleft.sub hright).eventually (gt_mem_nhds (sub_neg.mpr (hoversize i))) |>.mono
      (fun z hz => sub_neg.mp hz)
  filter_upwards [hli, hord, hcor, Filter.eventually_all.mpr hscalar] with z hz ho hc hh
  exact ⟨hz, ho, hc, hh⟩

/-- Actual ModelStep retains a complete independent unrefuted window
whenever capacity allows it. Its deletion counters are computed correctly. -/
theorem algorithmModel_retains_of_window {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hLI : LinearIndependent ℝ (storedSteps S.pairs))
    (hcap : S.pairs.length ≤ min S.capacity n)
    (hpass : windowUnrefuted P.windowThreshold (storedPairing S.pairs)) :
    (algorithmModel P S).pairs = S.pairs ∧
      (algorithmModel P S).pairsBeforeTest = S.pairs.length ∧
      (algorithmModel P S).deletedByTest = 0 := by
  have hretain : retainNewest (min S.capacity n) S.pairs = S.pairs := by
    simp only [retainNewest, Nat.sub_eq_zero_of_le hcap, List.drop_zero]
  have hrank : rankWindow n S = S.pairs := by
    simp only [rankWindow, hretain, rankDeletion_eq_zero S.pairs hLI, List.drop_zero]
  have hdelete := modelDeletion_eq_zero P S.pairs hpass
  simp only [algorithmModel, hrank, hdelete, List.drop_zero, and_self]

/-- Actual endpoint test success is actual native list test success. All
casts transport the real pair matrix and its corrected diagonal together. -/
theorem endpointObservations_tests {n k : ℕ} (P : Parameters)
    (C : EndpointChart (EuclideanSpace ℝ (Fin n)) k)
    (hLI : LinearIndependent ℝ (endpointStep C))
    (hordinary : (endpointHermitianTest P.windowThreshold false C).PosDef)
    (hcorrected : (endpointHermitianTest P.windowThreshold true C).PosDef)
    (hoversize : ∀ i, |12 * endpointSplit C i * endpointDefect C i| ≤
      inner ℝ (endpointStep C i) (endpointImage C i) / 2) :
    LinearIndependent ℝ (storedSteps (endpointObservations C)) ∧
      windowUnrefuted P.windowThreshold (storedPairing (endpointObservations C)) ∧
      (∀ i : Fin (endpointObservations C).length,
        |12 * storedSplit (endpointObservations C) i * ((endpointObservations C).get i).valueDefect| ≤
          storedPairing (endpointObservations C) i i / 2) ∧
      correctedWindowPasses P.windowThreshold (endpointObservations C) := by
  let W := endpointObservations C
  let e := finCongr (endpointObservations_length C)
  have he : StrictMono e := by intro i j hij; exact hij
  have hgate (i : Fin W.length) :
      |12 * storedSplit W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2 := by
    change |12 * storedSplit (endpointObservations C) i * ((endpointObservations C).get i).valueDefect| ≤
      storedPairing (endpointObservations C) i i / 2
    simp only [storedSplit, endpointObservations_get, storedPairing,
      endpointObservations_steps, endpointObservations_images, crossGram, Function.comp_apply]
    exact hoversize (e i)
  refine ⟨?_, ?_, hgate, ?_⟩
  · rw [endpointObservations_steps]
    exact hLI.comp e e.injective
  · rw [endpointObservations_pairing]
    apply windowUnrefuted_submatrix _ _ e he
    change (hermitianWindowMatrix P.windowThreshold (crossGram (endpointStep C) (endpointImage C))).PosDef
    simpa only [endpointHermitianTest, endpointVirtualModel, Bool.false_eq_true, ite_false,
      diagonal_zero, sub_zero, hermitianWindowMatrix] using hordinary
  · have hmodel : storedExactValueModel W = (endpointVirtualModel true C).submatrix e e := by
      have hm := endpointObservations_model {P with valuesEnabled := true} C
      simpa only [fullVirtualSelectedModel, ite_true] using hm
    rw [correctedWindowPasses, storedValueModel_eq_exact W hgate, hmodel, endpointObservations_pairing]
    change ((endpointHermitianTest P.windowThreshold true C).submatrix e e).PosDef
    exact hcorrected.submatrix e.injective

end
end krylov.XR
