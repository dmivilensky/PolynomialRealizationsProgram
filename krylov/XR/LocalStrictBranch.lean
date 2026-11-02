import krylov.XR.LocalHistoryTests
import krylov.XR.LocalHistoryProgram
import krylov.XR.LocalNativeChart

/-!
Article: main_krylov, lem:xr-local, actual strict finite decisions.
Use: represent the real safeguard, Armijo and positive-secant decisions
directly in genuine endpoint observations, and prove their neighbourhood
stability. These predicates are mathematical branch sets, never fields of
the algorithm or source function.
Source: strict scalar continuity and the proved actual Hermitian domains.
-/

namespace krylov.XR
noncomputable section
open Matrix Filter Topology krylov.Methods
open scoped InnerProductSpace ComplexOrder
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Strict original scalar decisions on one actual endpoint transition.
The positive-secant component is a test of the real next gradient, rather
than a compatible-operator certificate. -/
def EndpointTransitionStrict {k : ℕ} (sigma c₁ c₂ : ℝ) (C : EndpointChart E (k + 1)) : Prop :=
  let g := C.2.2 (Fin.last k).castSucc
  let u := endpointStep C (Fin.last k)
  inner ℝ g u < 0 ∧ inner ℝ g u < -c₁ * ‖g‖ ^ 2 ∧ ‖u‖ < c₂ * ‖g‖ ∧
    C.2.1 (Fin.last (k + 1)) < C.2.1 (Fin.last k).castSucc + sigma * inner ℝ g u ∧
    0 < inner ℝ u (endpointImage C (Fin.last k))

/-- Exactly the source's strict safeguard and Armijo inequalities at a
reference transition. Positive quadratic secants are derived separately. -/
def EndpointTransitionCoreStrict {k : ℕ} (sigma c₁ c₂ : ℝ) (C : EndpointChart E (k + 1)) : Prop :=
  let g := C.2.2 (Fin.last k).castSucc
  let u := endpointStep C (Fin.last k)
  inner ℝ g u < -c₁ * ‖g‖ ^ 2 ∧ ‖u‖ < c₂ * ‖g‖ ∧
    C.2.1 (Fin.last (k + 1)) < C.2.1 (Fin.last k).castSucc + sigma * inner ℝ g u

/-- The original strict inequalities force a negative true slope;
genuine positive observed curvature supplies the last scalar branch. -/
theorem endpointTransitionStrict_of_core {k : ℕ} (sigma c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁)
    (C : EndpointChart E (k + 1)) (h : EndpointTransitionCoreStrict sigma c₁ c₂ C)
    (hpositive : 0 < inner ℝ (endpointStep C (Fin.last k)) (endpointImage C (Fin.last k))) :
    EndpointTransitionStrict sigma c₁ c₂ C := by
  have hn : -c₁ * ‖C.2.2 (Fin.last k).castSucc‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc₁) (sq_nonneg _)
  exact ⟨h.1.trans_le hn, h.1, h.2.1, h.2.2, hpositive⟩

omit [NormedSpace ℝ X] in
/-- Strict true safeguard and Armijo inequalities and true positive
curvature persist under continuous actual endpoint observations. -/
theorem endpointTransitionStrict_eventually {k : ℕ}
    (sigma c₁ c₂ : ℝ) (C : X → EndpointChart E (k + 1)) (x : X)
    (hC : ContinuousAt C x) (hstrict : EndpointTransitionStrict sigma c₁ c₂ (C x)) :
    ∀ᶠ z in 𝓝 x, EndpointTransitionStrict sigma c₁ c₂ (C z) := by
  have hp (i : Fin (k + 2)) : ContinuousAt (fun z => (C z).1 i) x :=
    (continuousAt_pi.mp hC.fst) i
  have hf (i : Fin (k + 2)) : ContinuousAt (fun z => (C z).2.1 i) x :=
    (continuousAt_pi.mp hC.snd.fst) i
  have hg (i : Fin (k + 2)) : ContinuousAt (fun z => (C z).2.2 i) x :=
    (continuousAt_pi.mp hC.snd.snd) i
  let u := fun z => endpointStep (C z) (Fin.last k)
  let g := fun z => (C z).2.2 (Fin.last k).castSucc
  have hu : ContinuousAt u x := (hp (Fin.last k).succ).sub (hp (Fin.last k).castSucc)
  have hgrad : ContinuousAt g x := hg (Fin.last k).castSucc
  have hslope : ContinuousAt (fun z => inner ℝ (g z) (u z)) x := hgrad.inner hu
  have hy : ContinuousAt (fun z => endpointImage (C z) (Fin.last k)) x :=
    (hg (Fin.last k).succ).sub (hg (Fin.last k).castSucc)
  have hcurv : ContinuousAt (fun z => inner ℝ (u z) (endpointImage (C z) (Fin.last k))) x := hu.inner hy
  have hlt (a b : X → ℝ) (ha : ContinuousAt a x) (hb : ContinuousAt b x) (h : a x < b x) :
      ∀ᶠ z in 𝓝 x, a z < b z := by
    exact (ha.sub hb).eventually (gt_mem_nhds (sub_neg.mpr h)) |>.mono (fun _ hz => sub_neg.mp hz)
  obtain ⟨hneg, hdescent, hnorm, harmijo, hpositive⟩ := hstrict
  have h₁ := hslope.eventually (gt_mem_nhds hneg)
  have h₂ := hlt _ _ hslope (continuousAt_const.mul (hgrad.norm.pow 2)) hdescent
  have h₃ := hlt _ _ hu.norm (continuousAt_const.mul hgrad.norm) hnorm
  have h₄ := hlt _ _ (hf (Fin.last (k + 1)))
    ((hf (Fin.last k).castSucc).add (continuousAt_const.mul hslope)) harmijo
  have h₅ := hcurv.eventually (lt_mem_nhds hpositive)
  filter_upwards [h₁, h₂, h₃, h₄, h₅] with z h₁ h₂ h₃ h₄ h₅
  exact ⟨h₁, h₂, h₃, h₄, h₅⟩

/-- The precise strict observed branch of a genuine finite full-memory
endpoint program. This definition only classifies computed transcripts. -/
def EndpointFiniteBranch (values : Bool) (trial : (k : ℕ) → EndpointChart E k → ℝ)
    (theta sigma c₁ c₂ : ℝ) (x₀ : E) (f₀ : ℝ) (g₀ : E) :
    (k : ℕ) → (Fin k → ℝ × E) → Prop
  | 0, _ => True
  | k + 1, data =>
    let C := endpointProgramChart values trial x₀ f₀ g₀ k (Fin.init data)
    EndpointFiniteBranch values trial theta sigma c₁ c₂ x₀ f₀ g₀ k (Fin.init data) ∧
      LinearIndependent ℝ (endpointStep C) ∧
      (endpointHermitianTest theta false C).PosDef ∧
      (endpointHermitianTest theta true C).PosDef ∧
      (∀ i, |12 * endpointSplit C i * endpointDefect C i| <
        inner ℝ (endpointStep C i) (endpointImage C i) / 2) ∧
      EndpointTransitionStrict sigma c₁ c₂
        (endpointProgramChart values trial x₀ f₀ g₀ (k + 1) data)

variable [CompleteSpace E]

/-- The actual finite strict branch is a neighbourhood of every genuine
reference transcript satisfying the primitive smooth-trial domains.
Smoothness of the computed trajectory and inverse solves is derived. -/
theorem endpointFiniteBranch_mem_nhds (values : Bool)
    (trial : (k : ℕ) → EndpointChart E k → ℝ)
    (theta sigma c₁ c₂ : ℝ) (x₀ : E) (f₀ : ℝ) (g₀ : E)
    (k : ℕ) (data : Fin k → ℝ × E)
    (hbranch : EndpointFiniteBranch values trial theta sigma c₁ c₂ x₀ f₀ g₀ k data)
    (hdomains : k = 0 ∨
      ∃ j : ℕ, ∃ h : k = j + 1,
        EndpointProgramDomain values trial x₀ f₀ g₀ 2 j
          (Fin.init (h ▸ data))) :
    {d | EndpointFiniteBranch values trial theta sigma c₁ c₂ x₀ f₀ g₀ k d} ∈ 𝓝 data := by
  induction k with
  | zero => exact Filter.univ_mem
  | succ k ih =>
    have hd : EndpointProgramDomain values trial x₀ f₀ g₀ 2 k (Fin.init data) := by
      rcases hdomains with he | ⟨j, he, hd⟩
      · omega
      · have hj : j = k := by omega
        subst j
        exact hd
    obtain ⟨hprevious, hLI, ho, hc, hs, ht⟩ := hbranch
    have hprevdomains : k = 0 ∨ ∃ j : ℕ, ∃ h : k = j + 1,
        EndpointProgramDomain values trial x₀ f₀ g₀ 2 j (Fin.init (h ▸ Fin.init data)) := by
      cases k with
      | zero => exact Or.inl rfl
      | succ k => exact Or.inr ⟨k, rfl, hd.1⟩
    have hi : ContinuousAt (fun d : Fin (k + 1) → ℝ × E => Fin.init d) data := by
      apply continuousAt_pi.mpr
      intro i
      exact (continuous_apply i.castSucc).continuousAt
    have hprevious' := hi.preimage_mem_nhds (ih (Fin.init data) hprevious hprevdomains)
    have hchart := (endpointProgram_contDiff values trial x₀ f₀ g₀ 2 k (Fin.init data) hd).1
    have hinit : ContDiffAt ℝ 2 (fun d : Fin (k + 1) → ℝ × E => Fin.init d) data := by
      apply contDiffAt_pi.mpr
      intro i
      exact contDiffAt_apply ℝ (ℝ × E) i.castSucc data
    have hcurrent := EndpointProgramDomain.current values trial x₀ f₀ g₀ 2 k (Fin.init data) hd
    have hcomp : ContDiffAt ℝ 2
        (fun d : Fin (k + 1) → ℝ × E => endpointProgramChart values trial x₀ f₀ g₀ k (Fin.init d)) data := by
      simpa only [Function.comp_def] using hchart.comp data hinit
    have htests := endpoint_model_tests_eventually theta
      (fun d : Fin (k + 1) → ℝ × E => endpointProgramChart values trial x₀ f₀ g₀ k (Fin.init d)) data
      hcomp hcurrent.2.1 hLI ho hc hs
    have htransition := endpointTransitionStrict_eventually sigma c₁ c₂ _ data
      (endpointProgramChart_succ_contDiff values trial x₀ f₀ g₀ 2 k data hd).continuousAt ht
    filter_upwards [hprevious', htests, htransition] with d hp hm ht
    exact ⟨hp, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2, ht⟩

end
end krylov.XR
