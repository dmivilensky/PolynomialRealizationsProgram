import krylov.XR.LocalHistoryChart
import krylov.XR.LocalOracleSource

/-!
Article: main_krylov, lem:xr-local, actual finite virtual-query program.
Use: chronological endpoint charts are built recursively from actual
value/gradient observations. Their C^r regularity is derived from the
primitive trial functions and the real observed inverse domains, rather
than assumed for the executed trajectory.
Source: finite induction and the proved genuine endpoint-coordinate solves.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods Filter Topology
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Add the next actual endpoint observation to a chronological chart. -/
def extendEndpointChart {k : ℕ} (C : EndpointChart E k) (point : E) (observation : ℝ × E) :
    EndpointChart E (k + 1) :=
  (Fin.snoc C.1 point, Fin.snoc C.2.1 observation.1, Fin.snoc C.2.2 observation.2)

/-- Literal data-only full-memory XRFC/F chart program. Its argument is
exactly the chronological sequence of actual endpoint oracle responses. -/
def endpointProgramChart (values : Bool) (trial : (k : ℕ) → EndpointChart E k → ℝ)
    (x₀ : E) (f₀ : ℝ) (g₀ : E) : (k : ℕ) → (Fin k → ℝ × E) → EndpointChart E k
  | 0, _ => (fun _ => x₀, fun _ => f₀, fun _ => g₀)
  | k + 1, data =>
    let C := endpointProgramChart values trial x₀ f₀ g₀ k (Fin.init data)
    extendEndpointChart C (endpointVirtualQuery values (trial k) C) (data (Fin.last k))

/-- The actual next oracle query of the endpoint-data executor. -/
def endpointProgramQuery (values : Bool) (trial : (k : ℕ) → EndpointChart E k → ℝ)
    (x₀ : E) (f₀ : ℝ) (g₀ : E) (k : ℕ) (data : Fin k → ℝ × E) : E :=
  endpointVirtualQuery values (trial k) (endpointProgramChart values trial x₀ f₀ g₀ k data)

/-- Genuine endpoint-array execution: each step evaluates the true scalar
and gradient at the computed physical query, and nowhere else. -/
def endpointFunctionRun (values : Bool) (trial : (k : ℕ) → EndpointChart E k → ℝ)
    (f : E → ℝ) (G : E → E) (x₀ : E) : (k : ℕ) → EndpointChart E k
  | 0 => (fun _ => x₀, fun _ => f x₀, fun _ => G x₀)
  | k + 1 =>
    let C := endpointFunctionRun values trial f G x₀ k
    let x := endpointVirtualQuery values (trial k) C
    extendEndpointChart C x (f x, G x)

omit [CompleteSpace E] in
/-- The adaptive data program and the genuine scalar executor are exactly
the same execution, rather than merely nearby trajectories. -/
theorem endpointFunctionRun_eq_program (values : Bool)
    (trial : (k : ℕ) → EndpointChart E k → ℝ) (f : E → ℝ) (G : E → E) (x₀ : E) (k : ℕ) :
    endpointFunctionRun values trial f G x₀ k =
      endpointProgramChart values trial x₀ (f x₀) (G x₀) k
        (adaptiveTranscript (endpointProgramQuery values trial x₀ (f x₀) (G x₀))
          (fun x => (f x, G x)) k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [adaptiveTranscript, endpointProgramChart, Fin.init_snoc, Fin.snoc_last,
      endpointFunctionRun, ih, endpointProgramQuery]

omit [CompleteSpace E] in
/-- Every cached scalar and gradient in the actual full-memory endpoint
executor is a genuine observation at its own computed endpoint. -/
theorem endpointFunctionRun_cache (values : Bool)
    (trial : (k : ℕ) → EndpointChart E k → ℝ) (f : E → ℝ) (G : E → E) (x₀ : E) (k : ℕ) :
    let C := endpointFunctionRun values trial f G x₀ k
    ∀ i, C.2.1 i = f (C.1 i) ∧ C.2.2 i = G (C.1 i) := by
  induction k with
  | zero => exact fun _ => ⟨rfl, rfl⟩
  | succ k ih =>
    dsimp only at ih ⊢
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [endpointFunctionRun, extendEndpointChart, Fin.snoc_last, and_self]
    · simpa only [endpointFunctionRun, extendEndpointChart, Fin.snoc_castSucc] using ih j

/-- Actual observed algebraic domains and the original primitive trial
smoothness at every prefix. There is no executed-query or output
regularity assertion in this domain predicate. -/
def EndpointProgramDomain (values : Bool) (trial : (k : ℕ) → EndpointChart E k → ℝ)
    (x₀ : E) (f₀ : ℝ) (g₀ : E) (r : WithTop ℕ∞) :
    (k : ℕ) → (Fin k → ℝ × E) → Prop
  | 0, data =>
    let C := endpointProgramChart values trial x₀ f₀ g₀ 0 data
    ContDiffAt ℝ r (trial 0) C ∧
      (∀ i, inner ℝ (endpointStep C i) (endpointImage C i) ≠ 0) ∧
      (endpointVirtualModel values C).det ≠ 0 ∧
      (crossGram (endpointImage C) (endpointStep C)).det ≠ 0
  | k + 1, data =>
    let C := endpointProgramChart values trial x₀ f₀ g₀ (k + 1) data
    EndpointProgramDomain values trial x₀ f₀ g₀ r k (Fin.init data) ∧
      ContDiffAt ℝ r (trial (k + 1)) C ∧
      (∀ i, inner ℝ (endpointStep C i) (endpointImage C i) ≠ 0) ∧
      (endpointVirtualModel values C).det ≠ 0 ∧
      (crossGram (endpointImage C) (endpointStep C)).det ≠ 0

omit [CompleteSpace E] in
/-- Extract only the current actual algebraic domain of a recursive
primitive trial program. Earlier prefix domains remain in the predicate. -/
theorem EndpointProgramDomain.current (values : Bool)
    (trial : (k : ℕ) → EndpointChart E k → ℝ) (x₀ : E) (f₀ : ℝ) (g₀ : E)
    (r : WithTop ℕ∞) (k : ℕ) (data : Fin k → ℝ × E)
    (h : EndpointProgramDomain values trial x₀ f₀ g₀ r k data) :
    let C := endpointProgramChart values trial x₀ f₀ g₀ k data
    ContDiffAt ℝ r (trial k) C ∧
      (∀ i, inner ℝ (endpointStep C i) (endpointImage C i) ≠ 0) ∧
      (endpointVirtualModel values C).det ≠ 0 ∧
      (crossGram (endpointImage C) (endpointStep C)).det ≠ 0 := by
  cases k with
  | zero => exact h
  | succ k => exact h.2

omit [CompleteSpace E] in
/-- A true next-endpoint append preserves C^r regularity componentwise. -/
theorem contDiff_extendEndpointChart {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {r : WithTop ℕ∞} (C : X → EndpointChart E k) (point : X → E)
    (observation : X → ℝ × E) (x : X) (hC : ContDiffAt ℝ r C x)
    (hp : ContDiffAt ℝ r point x) (ho : ContDiffAt ℝ r observation x) :
    ContDiffAt ℝ r (fun z => extendEndpointChart (C z) (point z) (observation z)) x := by
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [extendEndpointChart, Fin.snoc_last] using hp
    · simpa only [extendEndpointChart, Fin.snoc_castSucc] using (contDiffAt_pi.mp hC.fst) j
  · apply ContDiffAt.prodMk
    · apply contDiffAt_pi.mpr
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [extendEndpointChart, Fin.snoc_last] using ho.fst
      · simpa only [extendEndpointChart, Fin.snoc_castSucc] using (contDiffAt_pi.mp hC.snd.fst) j
    · apply contDiffAt_pi.mpr
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [extendEndpointChart, Fin.snoc_last] using ho.snd
      · simpa only [extendEndpointChart, Fin.snoc_castSucc] using (contDiffAt_pi.mp hC.snd.snd) j
/-- Finite primitive trial smoothness and genuine inverse domains imply
smoothness of the actual recursively computed endpoint chart and query. -/
theorem endpointProgram_contDiff (values : Bool)
    (trial : (k : ℕ) → EndpointChart E k → ℝ) (x₀ : E) (f₀ : ℝ) (g₀ : E)
    (r : WithTop ℕ∞) (k : ℕ) (data : Fin k → ℝ × E)
    (h : EndpointProgramDomain values trial x₀ f₀ g₀ r k data) :
    ContDiffAt ℝ r (endpointProgramChart values trial x₀ f₀ g₀ k) data ∧
      ContDiffAt ℝ r (endpointProgramQuery values trial x₀ f₀ g₀ k) data := by
  induction k with
  | zero =>
    have hc : ContDiffAt ℝ r (endpointProgramChart values trial x₀ f₀ g₀ 0) data :=
      contDiffAt_const
    exact ⟨hc, contDiff_endpointVirtualQuery values _ (trial 0) data hc h.1 h.2.1 h.2.2.1 h.2.2.2⟩
  | succ k ih =>
    obtain ⟨hprevious, ht, hq, hm, hy⟩ := h
    obtain ⟨hc, hnext⟩ := ih (Fin.init data) hprevious
    have hinit : ContDiffAt ℝ r (fun d : Fin (k + 1) → ℝ × E => Fin.init d) data := by
      apply contDiffAt_pi.mpr
      intro i
      exact contDiffAt_apply ℝ (ℝ × E) i.castSucc data
    have hp := hc.comp data hinit
    have hnew := hnext.comp data hinit
    have he : ContDiffAt ℝ r (fun d : Fin (k + 1) → ℝ × E => d (Fin.last k)) data :=
      contDiffAt_apply ℝ (ℝ × E) (Fin.last k) data
    have hchart : ContDiffAt ℝ r (endpointProgramChart values trial x₀ f₀ g₀ (k + 1)) data := by
      apply ContDiffAt.prodMk
      · apply contDiffAt_pi.mpr
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [endpointProgramChart, extendEndpointChart, Fin.snoc_last,
            Function.comp_def, endpointProgramQuery] using hnew
        · simpa only [endpointProgramChart, extendEndpointChart, Fin.snoc_castSucc, Function.comp_def] using
            (contDiffAt_pi.mp hp.fst) j
      · apply ContDiffAt.prodMk
        · apply contDiffAt_pi.mpr
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa only [endpointProgramChart, extendEndpointChart, Fin.snoc_last] using he.fst
          · simpa only [endpointProgramChart, extendEndpointChart, Fin.snoc_castSucc, Function.comp_def] using
              (contDiffAt_pi.mp hp.snd.fst) j
        · apply contDiffAt_pi.mpr
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa only [endpointProgramChart, extendEndpointChart, Fin.snoc_last] using he.snd
          · simpa only [endpointProgramChart, extendEndpointChart, Fin.snoc_castSucc, Function.comp_def] using
              (contDiffAt_pi.mp hp.snd.snd) j
    exact ⟨hchart, contDiff_endpointVirtualQuery values _ (trial (k + 1)) data hchart ht hq hm hy⟩

/-- Smoothness of the last observed chart needs domains only at the
previous queried window; no extra trial smoothness at a terminal full
window is introduced into the original finite-cycle assumptions. -/
theorem endpointProgramChart_succ_contDiff (values : Bool)
    (trial : (k : ℕ) → EndpointChart E k → ℝ) (x₀ : E) (f₀ : ℝ) (g₀ : E)
    (r : WithTop ℕ∞) (k : ℕ) (data : Fin (k + 1) → ℝ × E)
    (h : EndpointProgramDomain values trial x₀ f₀ g₀ r k (Fin.init data)) :
    ContDiffAt ℝ r (endpointProgramChart values trial x₀ f₀ g₀ (k + 1)) data := by
  obtain ⟨hc, hq⟩ := endpointProgram_contDiff values trial x₀ f₀ g₀ r k (Fin.init data) h
  have hi : ContDiffAt ℝ r (fun d : Fin (k + 1) → ℝ × E => Fin.init d) data := by
    apply contDiffAt_pi.mpr
    intro i
    exact contDiffAt_apply ℝ (ℝ × E) i.castSucc data
  have he := contDiffAt_apply ℝ (ℝ × E) (Fin.last k) data (n := r)
  exact contDiff_extendEndpointChart _ _ _ data (hc.comp data hi) (hq.comp data hi) he

/-- Under the original finite smooth-trial and actual inverse-domain
conditions, a genuine Hessian-small perturbation preserves every open
strict branch and encloses all actual full-memory virtual queries. -/
theorem endpointProgram_source_open_branch
    (values : Bool) (trial : (k : ℕ) → EndpointChart E k → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (g₀ : E) (constant : ℝ)
    (N : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (hdomains : ∀ k < N, EndpointProgramDomain values trial 0 constant g₀ 2 k
      (adaptiveTranscript (endpointProgramQuery values trial 0 constant g₀)
        (fun x => (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)) k))
    (hpoints : ∀ k < N,
      adaptivePoint (endpointProgramQuery values trial 0 constant g₀)
        (fun x => (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)) k ∈ Metric.ball 0 radius)
    (V : Set (Fin N → ℝ × E))
    (hV : V ∈ 𝓝 (adaptiveTranscript (endpointProgramQuery values trial 0 constant g₀)
      (fun x => (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)) N)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E),
      f 0 = quadraticObjective Q g₀ constant 0 → G 0 = g₀ →
      (∀ z ∈ Metric.ball 0 radius, HasFDerivAt f (innerSL ℝ (G z)) z) →
      (∀ z ∈ Metric.ball 0 radius, HasFDerivAt G (H z) z) →
      (∀ z ∈ Metric.ball 0 radius, ‖H z - Q‖ ≤ epsilon) →
      (∀ k < N, adaptivePoint (endpointProgramQuery values trial 0 constant g₀)
        (fun x => (f x, G x)) k ∈ Metric.ball 0 radius) ∧
      adaptiveTranscript (endpointProgramQuery values trial 0 constant g₀)
        (fun x => (f x, G x)) N ∈ V := by
  apply finite_scalar_source_open_branch Q hQ g₀ constant _ N radius hradius
    (fun k hk => (endpointProgram_contDiff values trial 0 constant g₀ 2 k _
      (hdomains k hk)).2.continuousAt) hpoints V hV

end
end krylov.XR
