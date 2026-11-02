import bezout.Algorithms.ScalarProgram
import bezout.Algorithms.BalancedPreparation

/-!
Article: bezout, Algorithm 2, linear scalar preparation work and storage.
Use: an actual single-assignment arithmetic program memoizes every Chebyshev
value, parity weight, normalizer, four-entry impulse band and reverse readout.
Proof: each arithmetic expression reads only earlier cache cells; local exact
recurrences identify the evaluated cache with the proved scalar preparation.
Arithmetic nodes count exact-real RAM operations; cache access is constant cost.
-/

namespace bezout.Algorithms.Balanced
noncomputable section
open Polynomial
open scoped BigOperators

local infixl:65 " +ₑ " => ScalarExpr.add
local infixl:65 " -ₑ " => ScalarExpr.sub
local infixl:70 " *ₑ " => ScalarExpr.mul
local infixl:70 " /ₑ " => ScalarExpr.div

/-- Ten forward cells at each degree: C, omega, Z, a, c, B and four raw impulses. -/
def forwardIndex (j f : ℕ) : ℕ := 10 * j + f

/-- Start of the reverse parity/readout cache. -/
def reverseBase (N : ℕ) : ℕ := 10 * (N + 1)

/-- Three reverse cells at each descending degree: P, Q and b. -/
def reverseIndex (N r f : ℕ) : ℕ := reverseBase N + 3 * r + f

/-- Exact number of scalar cells allocated by the memoized preparation. -/
def scalarCells (N : ℕ) : ℕ := reverseBase N + 3 * N

/-- Cached access to a forward scalar cell. -/
def forwardRead (j f : ℕ) : ScalarExpr := .read (forwardIndex j f)

/-- Inputs are eta and Delta; all remaining external words are horizon/degree indices. -/
def scalarInputs (I : chebyshev1.SpectralInterval) (i : ℕ) : ℝ :=
  if i = 0 then I.eta else if i = 1 then I.delta else 0

/-- The exact parity weight, expanded into a fixed-size arithmetic expression. -/
def omegaExpr (N j : ℕ) : ScalarExpr :=
  if j < 2 then .constant 1 else
    if Even N then
      ((.constant N +ₑ .constant 2) -ₑ .constant j -ₑ .constant ((j % 2 : ℕ) : ℝ)) /ₑ .constant N
    else if Even j then
      (.constant N +ₑ .constant 1) *ₑ ((.constant N +ₑ .constant 1) -ₑ .constant j) /ₑ
        (.constant N *ₑ .constant N +ₑ .constant 1)
    else ((.constant N +ₑ .constant 2) -ₑ .constant j) /ₑ (.constant N +ₑ .constant 1)

/-- A previous raw impulse is either causally zero or a cached entry in the four-band table. -/
def pastImpulseExpr (j d r : ℕ) : ScalarExpr :=
  if r < d then forwardRead (j-r) (5+d-r) else .constant 0

/-- The three third-row startup entries use only cached omega and Z values. -/
def startupImpulseExpr (j d : ℕ) : ScalarExpr :=
  if j = 1 then .constant (-2) /ₑ .input 1 else
  if j = 2 then .constant (-4) *ₑ .input 0 *ₑ forwardRead 2 1 /ₑ .input 1 else
  if d = 1 then .constant (-4) *ₑ forwardRead 3 1 *ₑ forwardRead 2 2 /ₑ
    (.input 1 *ₑ forwardRead 2 1) else
  if d = 2 then .constant (-8) *ₑ .input 0 *ₑ .input 0 *ₑ forwardRead 3 1 /ₑ .input 1 else
    .constant (-2) /ₑ .input 1 +ₑ forwardRead 3 1 *ₑ
      (.constant (-8) *ₑ .input 0 *ₑ .input 0 /ₑ .input 1 +ₑ
        .constant 4 /ₑ (.input 1 *ₑ forwardRead 2 1))

/-- One exact arithmetic expression for a raw impulse in the stored causal band. -/
def impulseExpr (N j d : ℕ) : ScalarExpr :=
  if j < N ∧ d ≤ j then
    if j < 4 then startupImpulseExpr j d else
      forwardRead j 3 *ₑ pastImpulseExpr j d 1 +ₑ
      (.constant 1 -ₑ forwardRead j 4) *ₑ pastImpulseExpr j d 2 -ₑ
      forwardRead j 3 *ₑ pastImpulseExpr j d 3 +ₑ
      forwardRead j 4 *ₑ pastImpulseExpr j d 4 -ₑ
      forwardRead j 5 *ₑ
        (forwardRead (j-1) 2 *ₑ .constant (if d = 1 then 1 else 0) -ₑ
         forwardRead (j-3) 2 *ₑ .constant (if d = 3 then 1 else 0))
  else .constant 0

/-- One forward cache row. The extra final row stores only C_N. -/
def forwardExpr (N j f : ℕ) : ScalarExpr :=
  if f = 0 then
    if j = 0 then .constant 1 else if j = 1 then .input 0 else
      .constant 2 *ₑ .input 0 *ₑ forwardRead (j-1) 0 -ₑ forwardRead (j-2) 0
  else if j < N then
    if f = 1 then omegaExpr N j else
    if f = 2 then
      if j = 0 then .constant 1 else if j = 1 then .input 0 else
        forwardRead (j-2) 2 +ₑ forwardRead j 1 *ₑ (forwardRead j 0 -ₑ forwardRead (j-2) 0)
    else if f = 3 then
      if 4 ≤ j then .constant 2 *ₑ .input 0 *ₑ forwardRead j 1 /ₑ forwardRead (j-1) 1 else .constant 0
    else if f = 4 then
      if 4 ≤ j then forwardRead j 1 /ₑ forwardRead (j-2) 1 else .constant 0
    else if f = 5 then
      if 4 ≤ j then .constant 4 *ₑ forwardRead j 1 /ₑ (.input 1 *ₑ forwardRead (j-1) 1) else .constant 0
    else impulseExpr N j (f-5)
  else .constant 0

/-- A reverse dependency skips two rows in the same parity, or uses the zero boundary. -/
def nextReverseRead (N r f : ℕ) : ScalarExpr :=
  if 2 ≤ r then .read (reverseIndex N (r-2) f) else .constant 0

/-- A descending P,Q,b row, with the final absent quotient explicitly omitted. -/
def reverseExpr (N r f : ℕ) : ScalarExpr :=
  let j := N-1-r
  if f = 0 then
    nextReverseRead N r 0 +ₑ .constant (bezout.Balanced.endpointWeight (N-1-j)) *ₑ forwardRead (N-1-j) 0
  else if f = 1 then
    nextReverseRead N r 1 +ₑ .constant (bezout.Balanced.endpointWeight j) *ₑ .read (reverseIndex N r 0) /ₑ .constant 2
  else
    .constant 4 *ₑ forwardRead j 2 /ₑ (forwardRead N 0 *ₑ .input 1) *ₑ
      (.read (reverseIndex N r 1) /ₑ forwardRead j 1 -ₑ
        if 2 ≤ r then nextReverseRead N r 1 /ₑ forwardRead (j+2) 1 else .constant 0)

/-- The chronological single-assignment node selected by its absolute cache location. -/
def scalarNode (N i : ℕ) : ScalarExpr :=
  if i < reverseBase N then forwardExpr N (i/10) (i%10) else
    reverseExpr N ((i-reverseBase N)/3) ((i-reverseBase N)%3)

/-- Parity-weight preparation reads no previously computed scalar. -/
theorem omegaExpr_reads (N j : ℕ) : (omegaExpr N j).reads = ∅ := by
  unfold omegaExpr
  split_ifs <;> rfl

/-- Every raw-band dependency is an earlier forward cache cell. -/
theorem impulseExpr_causal {N j d f q : ℕ} (hd1 : 1 ≤ d) (hd4 : d ≤ 4)
    (hf : f = 5+d) (hq : q ∈ (impulseExpr N j d).reads) : q < forwardIndex j f := by
  by_cases hg : j < N ∧ d ≤ j
  · rw [impulseExpr, ite_eq_left hg] at hq
    by_cases hs : j < 4
    · rw [ite_eq_left hs] at hq
      unfold startupImpulseExpr at hq
      split_ifs at hq
      all_goals simp [ScalarExpr.reads, forwardRead] at hq
      all_goals unfold forwardIndex at *
      all_goals omega
    · rw [ite_eq_right hs] at hq
      simp only [pastImpulseExpr] at hq
      split_ifs at hq
      all_goals simp [ScalarExpr.reads, forwardRead] at hq
      all_goals unfold forwardIndex at *
      all_goals omega
  · simp [impulseExpr, hg, ScalarExpr.reads] at hq

/-- Every forward node reads only cells already cached at its exact execution point. -/
theorem forwardExpr_causal {N j f q : ℕ} (hf : f < 10)
    (hq : q ∈ (forwardExpr N j f).reads) : q < forwardIndex j f := by
  by_cases hlow : f ≤ 5
  · interval_cases f
    all_goals norm_num only [forwardExpr] at hq
    all_goals split_ifs at hq
    all_goals simp [ScalarExpr.reads, forwardRead, omegaExpr_reads] at hq
    all_goals unfold forwardIndex at *
    all_goals omega
  · have h0 : f ≠ 0 := by omega
    have h1 : f ≠ 1 := by omega
    have h2 : f ≠ 2 := by omega
    have h3 : f ≠ 3 := by omega
    have h4 : f ≠ 4 := by omega
    have h5 : f ≠ 5 := by omega
    by_cases hj : j < N
    · simp only [forwardExpr, h0, h1, h2, h3, h4, h5, hj, ite_false, ite_true] at hq
      exact impulseExpr_causal (by omega) (by omega) (by omega) hq
    · simp [forwardExpr, h0, hj, ScalarExpr.reads] at hq

/-- Reverse parity dependencies and same-row P/Q dependencies are all earlier cells. -/
theorem reverseExpr_causal {N r f q : ℕ} (hr : r < N) (hf : f < 3)
    (hq : q ∈ (reverseExpr N r f).reads) : q < reverseIndex N r f := by
  interval_cases f
  all_goals norm_num only [reverseExpr, nextReverseRead] at hq
  all_goals split_ifs at hq
  all_goals simp [ScalarExpr.reads, forwardRead] at hq
  all_goals unfold forwardIndex reverseIndex reverseBase at *
  all_goals omega

/-- The complete arithmetic DAG is a genuinely topological cached scalar program. -/
def scalarProgram (N : ℕ) : ScalarProgram (scalarCells N) where
  node i := scalarNode N i.val
  causal i q hq := by
    unfold scalarNode at hq
    split_ifs at hq with hi
    · have hf : i.val % 10 < 10 := Nat.mod_lt _ (by omega)
      have hh := forwardExpr_causal hf hq
      have he : forwardIndex (i.val/10) (i.val%10) = i.val := by
        unfold forwardIndex
        omega
      simpa only [he] using hh
    · have hr : (i.val-reverseBase N)/3 < N := by
        have hs := i.isLt
        unfold scalarCells at hs
        omega
      have hf : (i.val-reverseBase N)%3 < 3 := Nat.mod_lt _ (by omega)
      have hh := reverseExpr_causal hr hf hq
      have he : reverseIndex N ((i.val-reverseBase N)/3) ((i.val-reverseBase N)%3) = i.val := by
        unfold reverseIndex
        omega
      simpa only [he] using hh

/-- Arithmetic work of one parity weight is universally bounded. -/
theorem omegaExpr_cost (N j : ℕ) : (omegaExpr N j).cost ≤ 8 := by
  unfold omegaExpr
  split_ifs <;> norm_num [ScalarExpr.cost]

/-- Each earlier-band lookup has no arithmetic work. -/
theorem pastImpulseExpr_cost (j d r : ℕ) : (pastImpulseExpr j d r).cost = 0 := by
  unfold pastImpulseExpr
  split_ifs <;> rfl

/-- Each startup band entry uses a fixed number of arithmetic operations. -/
theorem startupImpulseExpr_cost (j d : ℕ) : (startupImpulseExpr j d).cost ≤ 16 := by
  unfold startupImpulseExpr
  split_ifs <;> norm_num [ScalarExpr.cost, forwardRead]

/-- A prepared band impulse has bounded work because every previous impulse is cached. -/
theorem impulseExpr_cost (N j d : ℕ) : (impulseExpr N j d).cost ≤ 32 := by
  unfold impulseExpr
  split_ifs
  all_goals try { exact (startupImpulseExpr_cost j d).trans (by omega) }
  all_goals norm_num [ScalarExpr.cost, forwardRead, pastImpulseExpr_cost]

/-- Forward cache entries require bounded scalar arithmetic independently of the horizon. -/
theorem forwardExpr_cost (N j f : ℕ) : (forwardExpr N j f).cost ≤ 64 := by
  unfold forwardExpr
  split_ifs
  all_goals try { exact (omegaExpr_cost N j).trans (by omega) }
  all_goals try { exact (impulseExpr_cost N j (f-5)).trans (by omega) }
  all_goals norm_num [ScalarExpr.cost, forwardRead]

/-- A reverse accumulator/readout cell has a fixed arithmetic-work bound. -/
theorem reverseExpr_cost (N r f : ℕ) : (reverseExpr N r f).cost ≤ 64 := by
  unfold reverseExpr nextReverseRead
  split_ifs <;> norm_num [ScalarExpr.cost, forwardRead]

/-- Every node has a universal arithmetic-operation bound, independent of the horizon. -/
theorem scalarNode_cost (N i : ℕ) : (scalarNode N i).cost ≤ 64 := by
  unfold scalarNode
  split_ifs
  · exact forwardExpr_cost N (i/10) (i%10)
  · exact reverseExpr_cost N ((i-reverseBase N)/3) ((i-reverseBase N)%3)

/-- The exact cache allocation is linear in the horizon. -/
theorem scalarCells_le {N : ℕ} (hN : 2 ≤ N) : scalarCells N ≤ 18*N := by
  unfold scalarCells reverseBase
  omega

/-- The actual arithmetic counter is linear because every cached node is evaluated once. -/
theorem scalarProgram_work_le (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    ((scalarProgram N).run (scalarInputs I)).cost ≤ 1152*N := by
  rw [ScalarProgram.run_cost]
  calc
    _ ≤ ∑ _i : Fin (scalarCells N), (64 : ℕ) :=
      Finset.sum_le_sum (fun i _ => scalarNode_cost N i.val)
    _ = scalarCells N * 64 := by simp
    _ ≤ (18*N)*64 := Nat.mul_le_mul_right 64 (scalarCells_le hN)
    _ = _ := by ring

/-- Semantic targets of the ten forward cache fields. -/
def forwardValue (I : chebyshev1.SpectralInterval) (N j f : ℕ) : ℝ :=
  if f = 0 then preparedC I j else
  if j < N then
    if f = 1 then bezout.Balanced.omega N j else
    if f = 2 then preparedNormalizer I N j else
    if f = 3 then if 4 ≤ j then 2 * I.eta * bezout.Balanced.omega N j / bezout.Balanced.omega N (j-1) else 0 else
    if f = 4 then if 4 ≤ j then bezout.Balanced.omega N j / bezout.Balanced.omega N (j-2) else 0 else
    if f = 5 then if 4 ≤ j then 4 * bezout.Balanced.omega N j / (I.delta * bezout.Balanced.omega N (j-1)) else 0 else
    if f-5 ≤ j then preparedImpulse I N j (j-(f-5)) else 0
  else 0

/-- Semantic targets of the reverse P,Q,b fields at one descending degree. -/
def reverseValue (I : chebyshev1.SpectralInterval) (N r f : ℕ) : ℝ :=
  let j := N-1-r
  if f = 0 then (preparedReverse I N j).1 else
  if f = 1 then (preparedReverse I N j).2 else preparedReadout I N j

/-- One natural-address target table for every cell of the concrete arithmetic program. -/
def scalarValue (I : chebyshev1.SpectralInterval) (N i : ℕ) : ℝ :=
  if i < reverseBase N then forwardValue I N (i/10) (i%10) else
    reverseValue I N ((i-reverseBase N)/3) ((i-reverseBase N)%3)

/-- Forward row decoding is exact at every allocated degree and field. -/
theorem scalarValue_forward (I : chebyshev1.SpectralInterval) {N j f : ℕ}
    (hj : j ≤ N) (hf : f < 10) :
    scalarValue I N (forwardIndex j f) = forwardValue I N j f := by
  have hi : forwardIndex j f < reverseBase N := by unfold forwardIndex reverseBase; omega
  have hd : forwardIndex j f / 10 = j := by unfold forwardIndex; omega
  have hm : forwardIndex j f % 10 = f := by unfold forwardIndex; omega
  simp only [scalarValue, hi, ite_true, hd, hm]

/-- Reverse row decoding is exact for all three allocated fields. -/
theorem scalarValue_reverse (I : chebyshev1.SpectralInterval) {N r f : ℕ}
    (hf : f < 3) : scalarValue I N (reverseIndex N r f) = reverseValue I N r f := by
  have hi : ¬reverseIndex N r f < reverseBase N := by unfold reverseIndex; omega
  have hd : (reverseIndex N r f-reverseBase N)/3 = r := by unfold reverseIndex; omega
  have hm : (reverseIndex N r f-reverseBase N)%3 = f := by unfold reverseIndex; omega
  simp only [scalarValue, hi, ite_false, hd, hm]

/-- Cached forward reads return the designated semantic field. -/
theorem forwardRead_eval (I : chebyshev1.SpectralInterval) {N j f : ℕ}
    (hj : j ≤ N) (hf : f < 10) :
    (forwardRead j f).eval (scalarInputs I) (scalarValue I N) = forwardValue I N j f :=
  scalarValue_forward I hj hf

/-- Arithmetic weight preparation exactly computes the displayed omega formula. -/
theorem omegaExpr_eval (I : chebyshev1.SpectralInterval) (N j : ℕ) :
    (omegaExpr N j).eval (scalarInputs I) (scalarValue I N) = bezout.Balanced.omega N j := by
  unfold omegaExpr bezout.Balanced.omega
  split_ifs <;> simp only [ScalarExpr.eval_add, ScalarExpr.eval_sub, ScalarExpr.eval_mul,
    ScalarExpr.eval_div, ScalarExpr.eval_constant]
  all_goals ring

/-- Cached first-kind values are exactly the already proved scalar C table. -/
theorem cache_C (I : chebyshev1.SpectralInterval) {N j : ℕ} (hj : j ≤ N) :
    (forwardRead j 0).eval (scalarInputs I) (scalarValue I N) = preparedC I j := by
  rw [forwardRead_eval I hj (by omega)]
  rfl

/-- Cached valid omega entries are the exact parity weights. -/
theorem cache_omega (I : chebyshev1.SpectralInterval) {N j : ℕ} (hj : j < N) :
    (forwardRead j 1).eval (scalarInputs I) (scalarValue I N) = bezout.Balanced.omega N j := by
  rw [forwardRead_eval I hj.le (by omega)]
  simp [forwardValue, hj]

/-- Cached valid Z entries are the exact prepared parity normalizers. -/
theorem cache_Z (I : chebyshev1.SpectralInterval) {N j : ℕ} (hj : j < N) :
    (forwardRead j 2).eval (scalarInputs I) (scalarValue I N) = preparedNormalizer I N j := by
  rw [forwardRead_eval I hj.le (by omega)]
  simp [forwardValue, hj]

/-- The four chronological impulse fields contain precisely their designated band entries. -/
theorem forwardValue_impulse (I : chebyshev1.SpectralInterval) {N j d : ℕ}
    (hj : j < N) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) :
    forwardValue I N j (5+d) = if d ≤ j then preparedImpulse I N j (j-d) else 0 := by
  have h0 : 5+d ≠ 0 := by omega
  have h1 : 5+d ≠ 1 := by omega
  have h2 : 5+d ≠ 2 := by omega
  have h3 : 5+d ≠ 3 := by omega
  have h4 : 5+d ≠ 4 := by omega
  have h5 : 5+d ≠ 5 := by omega
  simp only [forwardValue, h0, h1, h2, h3, h4, h5, hj, ite_true, ite_false,
    show 5+d-5=d by omega]

/-- A cached previous impulse agrees with the dense preparation, including its causal zeros. -/
theorem pastImpulseExpr_eval (I : chebyshev1.SpectralInterval) {N j d r : ℕ}
    (hN : 2 ≤ N) (hj : j < N) (hj4 : 4 ≤ j) (hd1 : 1 ≤ d) (hd4 : d ≤ 4)
    (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    (pastImpulseExpr j d r).eval (scalarInputs I) (scalarValue I N) =
      preparedImpulse I N (j-r) (j-d) := by
  by_cases hr : r < d
  · rw [pastImpulseExpr, ite_eq_left hr]
    have hf : 5+d-r=5+(d-r) := by omega
    rw [hf, forwardRead_eval I (by omega) (by omega),
      forwardValue_impulse I (by omega) (by omega) (by omega),
      ite_eq_left (show d-r ≤ j-r by omega), show j-r-(d-r)=j-d by omega]
  · rw [pastImpulseExpr, ite_eq_right hr, ScalarExpr.eval_constant]
    symm
    exact preparedImpulse_triangular I N hN ⟨j-r, by omega⟩ ⟨j-d, by omega⟩ (by exact show j-r ≤ j-d by omega)

/-- Startup-band expressions reproduce the actual printed scalar startup table. -/
theorem startupImpulseExpr_eval (I : chebyshev1.SpectralInterval) {N j d : ℕ}
    (hj : j < N) (hj4 : j < 4) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) (hdj : d ≤ j) :
    (startupImpulseExpr j d).eval (scalarInputs I) (scalarValue I N) =
      preparedImpulse I N j (j-d) := by
  interval_cases j
  · omega
  · have hd : d=1 := by omega
    subst d
    simp [startupImpulseExpr, preparedImpulse, scalarInputs]
  · interval_cases d
    all_goals simp (disch := omega) [startupImpulseExpr, preparedImpulse,
      scalarInputs, cache_omega]
  · interval_cases d
    all_goals simp (disch := omega) [startupImpulseExpr, preparedImpulse,
      scalarInputs, cache_omega, cache_Z, bezout.Balanced.startup30, bezout.Balanced.startup31]
    all_goals ring_nf
    all_goals simp

/-- Every evaluated band expression equals its memoized scalar-preparation target. -/
theorem impulseExpr_eval (I : chebyshev1.SpectralInterval) {N j d : ℕ}
    (hN : 2 ≤ N) (hj : j < N) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) :
    (impulseExpr N j d).eval (scalarInputs I) (scalarValue I N) =
      if d ≤ j then preparedImpulse I N j (j-d) else 0 := by
  by_cases hdj : d ≤ j
  · rw [impulseExpr, ite_eq_left ⟨hj, hdj⟩]
    by_cases hj4 : j < 4
    · rw [ite_eq_left hj4, ite_eq_left hdj]
      exact startupImpulseExpr_eval I hj hj4 hd1 hd4 hdj
    · rw [ite_eq_right hj4, ite_eq_left hdj]
      obtain ⟨s, rfl⟩ : ∃ s, j = s+4 := ⟨j-4, by omega⟩
      simp only [ScalarExpr.eval_add, ScalarExpr.eval_sub, ScalarExpr.eval_mul,
        ScalarExpr.eval_constant]
      simp (disch := omega) only [pastImpulseExpr_eval I hN,
        forwardRead_eval I, forwardValue, ite_true]
      rw [preparedImpulse]
      unfold bezout.Balanced.recurrenceA bezout.Balanced.recurrenceC bezout.Balanced.recurrenceB
      have h31 : s+4-1=s+3 := by omega
      have h32 : s+4-2=s+2 := by omega
      have h33 : s+4-3=s+1 := by omega
      have h34 : s+4-4=s := by omega
      have hk1 : ((s+4-d)=s+3) ↔ d=1 := by omega
      have hk3 : ((s+4-d)=s+1) ↔ d=3 := by omega
      have hj3 : s+3<N := by omega
      have hj1 : s+1<N := by omega
      simp [hj, hj3, hj1, h31, h32, h33, h34, hk1, hk3]
  · simp [impulseExpr, hj, hdj, ScalarExpr.eval_constant]

/-- Subtraction-index form of the prepared C recurrence used by the chronological DAG. -/
theorem preparedC_step (I : chebyshev1.SpectralInterval) {j : ℕ} (hj : 2 ≤ j) :
    preparedC I j = 2 * I.eta * preparedC I (j-1) - preparedC I (j-2) := by
  obtain ⟨s, rfl⟩ : ∃ s, j=s+2 := ⟨j-2, by omega⟩
  rw [preparedC, show s+2-1=s+1 by omega, Nat.add_sub_cancel]

/-- Subtraction-index form of the exact parity normalizer update. -/
theorem preparedNormalizer_step (I : chebyshev1.SpectralInterval) (N : ℕ) {j : ℕ}
    (hj : 2 ≤ j) : preparedNormalizer I N j = preparedNormalizer I N (j-2) +
      bezout.Balanced.omega N j * (preparedC I j - preparedC I (j-2)) := by
  obtain ⟨s, rfl⟩ : ∃ s, j=s+2 := ⟨j-2, by omega⟩
  simp only [preparedNormalizer, Nat.add_sub_cancel]

/-- Every forward arithmetic node computes its exact prepared target using cached reads. -/
theorem forwardExpr_eval (I : chebyshev1.SpectralInterval) {N j f : ℕ}
    (hN : 2 ≤ N) (hj : j ≤ N) (hf : f < 10) :
    (forwardExpr N j f).eval (scalarInputs I) (scalarValue I N) = forwardValue I N j f := by
  by_cases hf0 : f=0
  · subst f
    by_cases h0 : j=0
    · subst j; simp [forwardExpr, forwardValue, preparedC]
    · by_cases h1 : j=1
      · subst j; simp [forwardExpr, forwardValue, preparedC, scalarInputs]
      · simp (disch := omega) only [forwardExpr, forwardValue, h0, h1, ite_true,
          ite_false, ScalarExpr.eval_sub, ScalarExpr.eval_mul, ScalarExpr.eval_constant,
          ScalarExpr.eval_input, scalarInputs, cache_C]
        exact (preparedC_step I (by omega)).symm
  · by_cases hjN : j < N
    · interval_cases f
      · omega
      · simp only [forwardExpr, forwardValue, hjN, Nat.reduceEqDiff, ite_true, ite_false]
        exact omegaExpr_eval I N j
      · by_cases h0 : j=0
        · subst j; simp [forwardExpr, forwardValue, preparedNormalizer, hjN]
        · by_cases h1 : j=1
          · subst j; simp [forwardExpr, forwardValue, preparedNormalizer, scalarInputs, hjN]
          · simp (disch := omega) only [forwardExpr, forwardValue, hjN, h0, h1,
              Nat.reduceEqDiff, ite_true, ite_false, ScalarExpr.eval_add, ScalarExpr.eval_sub,
              ScalarExpr.eval_mul, cache_Z, cache_C, cache_omega]
            exact (preparedNormalizer_step I N (by omega)).symm
      · by_cases hj4 : 4 ≤ j
        all_goals simp (disch := omega) [forwardExpr, forwardValue, hjN, hj4,
          scalarInputs, cache_omega]
      · by_cases hj4 : 4 ≤ j
        all_goals simp (disch := omega) [forwardExpr, forwardValue, hjN, hj4, cache_omega]
      · by_cases hj4 : 4 ≤ j
        all_goals simp (disch := omega) [forwardExpr, forwardValue, hjN, hj4,
          scalarInputs, cache_omega]
      · simpa only [forwardExpr, forwardValue, hjN, Nat.reduceEqDiff, ite_true, ite_false,
          Nat.reduceSub] using impulseExpr_eval I hN hjN (d := 1) (by omega) (by omega)
      · simpa only [forwardExpr, forwardValue, hjN, Nat.reduceEqDiff, ite_true, ite_false,
          Nat.reduceSub] using impulseExpr_eval I hN hjN (d := 2) (by omega) (by omega)
      · simpa only [forwardExpr, forwardValue, hjN, Nat.reduceEqDiff, ite_true, ite_false,
          Nat.reduceSub] using impulseExpr_eval I hN hjN (d := 3) (by omega) (by omega)
      · simpa only [forwardExpr, forwardValue, hjN, Nat.reduceEqDiff, ite_true, ite_false,
          Nat.reduceSub] using impulseExpr_eval I hN hjN (d := 4) (by omega) (by omega)
    · simp [forwardExpr, forwardValue, hf0, hjN]

/-- The reverse scalar recursion has its literal zero boundary after the horizon. -/
theorem preparedReverse_terminal (I : chebyshev1.SpectralInterval) {N j : ℕ} (hj : N ≤ j) :
    preparedReverse I N j = (0,0) := by
  rw [preparedReverse, dite_eq_right (show ¬j<N by omega)]

/-- Reverse cache reads select the exact same-parity successor accumulator. -/
theorem nextReverseRead_eval (I : chebyshev1.SpectralInterval) {N r f : ℕ}
    (hr : r < N) (hf : f < 2) :
    (nextReverseRead N r f).eval (scalarInputs I) (scalarValue I N) =
      if f=0 then (preparedReverse I N (N-1-r+2)).1 else (preparedReverse I N (N-1-r+2)).2 := by
  by_cases hr2 : 2 ≤ r
  · have hj : N-1-(r-2)=N-1-r+2 := by omega
    rw [nextReverseRead, ite_eq_left hr2, ScalarExpr.eval_read, scalarValue_reverse I (by omega)]
    interval_cases f <;> simp only [reverseValue, hj, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [nextReverseRead, ite_eq_right hr2, ScalarExpr.eval_constant,
      preparedReverse_terminal I (by omega)]
    split_ifs <;> rfl

/-- Every descending P,Q,b node computes the exact prepared reverse/readout value. -/
theorem reverseExpr_eval (I : chebyshev1.SpectralInterval) {N r f : ℕ}
    (hr : r < N) (hf : f < 3) :
    (reverseExpr N r f).eval (scalarInputs I) (scalarValue I N) = reverseValue I N r f := by
  have hj : N-1-r < N := by omega
  have hs := preparedReverse_eq I N (N-1-r)
  have hp := bezout.Balanced.reverseP_step I hj
  have hq := bezout.Balanced.reverseQ_step I hj
  have hprep := preparedReverse_eq I N (N-1-r+2)
  interval_cases f
  · simp (disch := omega) only [reverseExpr, reverseValue, ScalarExpr.eval_add,
      ScalarExpr.eval_mul, ScalarExpr.eval_constant, nextReverseRead_eval I hr,
      cache_C, ite_true]
    rw [preparedC_eq, hs, hprep]
    exact hp.symm
  · simp (disch := omega) only [reverseExpr, reverseValue, ScalarExpr.eval_add,
      ScalarExpr.eval_mul, ScalarExpr.eval_div, ScalarExpr.eval_constant, ScalarExpr.eval_read,
      scalarValue_reverse I, nextReverseRead_eval I hr, Nat.reduceEqDiff, ite_false, ite_true]
    rw [hs, hprep]
    exact hq.symm
  · have ht : (2 ≤ r) ↔ N-1-r+2<N := by omega
    have hC : 1 / preparedC I N = I.epsilon N := by rw [preparedC_eq]; rfl
    have hCi : (preparedC I N)⁻¹ = I.epsilon N := by simpa only [one_div] using hC
    simp (disch := omega) only [reverseExpr, reverseValue,
      ScalarExpr.eval_sub, ScalarExpr.eval_mul, ScalarExpr.eval_div, ScalarExpr.eval_constant,
      ScalarExpr.eval_input, ScalarExpr.eval_read, scalarValue_reverse I,
      cache_C, cache_Z, cache_omega, Nat.reduceEqDiff, ite_false, scalarInputs, ite_true]
    by_cases hr2 : 2 ≤ r
    · rw [ite_eq_left hr2, ScalarExpr.eval_div, nextReverseRead_eval I hr (f := 1) (by omega)]
      simp only [Nat.reduceEqDiff, ite_false]
      rw [cache_omega I (ht.mp hr2)]
      rw [preparedReadout, ite_eq_left (ht.mp hr2)]
      simp only [div_eq_mul_inv, mul_inv_rev, hCi]
      ring
    · rw [ite_eq_right hr2, preparedReadout, ite_eq_right (by omega : ¬N-1-r+2<N)]
      simp only [ScalarExpr.eval_constant, div_eq_mul_inv, mul_inv_rev, hCi]
      ring

/-- Every concrete topological node evaluates to the designated prepared scalar. -/
theorem scalarNode_eval (I : chebyshev1.SpectralInterval) {N i : ℕ}
    (hN : 2 ≤ N) (hi : i < scalarCells N) :
    (scalarNode N i).eval (scalarInputs I) (scalarValue I N) = scalarValue I N i := by
  unfold scalarNode scalarValue
  split_ifs with hf
  · apply forwardExpr_eval I hN
    · unfold reverseBase at hf
      omega
    · exact Nat.mod_lt _ (by omega)
  · apply reverseExpr_eval I
    · unfold scalarCells at hi
      omega
    · exact Nat.mod_lt _ (by omega)

/-- The actual one-pass cached execution computes all prepared scalar tables exactly. -/
theorem scalarProgram_values (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    ((scalarProgram N).run (scalarInputs I)).values = fun i => scalarValue I N i.val := by
  apply ScalarProgram.run_correct_nat
  intro i
  exact scalarNode_eval I hN i.isLt

/-- Read an actual computed scalar cell, rather than reevaluating a recursive preparation. -/
def cachedScalar (I : chebyshev1.SpectralInterval) (N i : ℕ) : ℝ :=
  ScalarProgram.extend ((scalarProgram N).run (scalarInputs I)).values i

/-- Actual cache access agrees with the semantic scalar table at every allocated address. -/
theorem cachedScalar_eq (I : chebyshev1.SpectralInterval) {N i : ℕ}
    (hN : 2 ≤ N) (hi : i < scalarCells N) : cachedScalar I N i = scalarValue I N i := by
  rw [cachedScalar, scalarProgram_values I hN]
  simp only [ScalarProgram.extend, dite_eq_left hi]

/-- A first-kind scalar retrieved from the actual cached preparation. -/
def cachedC (I : chebyshev1.SpectralInterval) (N j : ℕ) : ℝ := cachedScalar I N (forwardIndex j 0)

/-- A parity weight retrieved from the actual cached preparation. -/
def cachedOmega (I : chebyshev1.SpectralInterval) (N j : ℕ) : ℝ := cachedScalar I N (forwardIndex j 1)

/-- A normalizer retrieved from the actual cached preparation. -/
def cachedZ (I : chebyshev1.SpectralInterval) (N j : ℕ) : ℝ := cachedScalar I N (forwardIndex j 2)

/-- A homogeneous fourth-order coefficient retrieved from its computed scalar cell. -/
def cachedA (I : chebyshev1.SpectralInterval) (N j : ℕ) : ℝ := cachedScalar I N (forwardIndex j 3)

/-- A parity-coupling coefficient retrieved from its computed scalar cell. -/
def cachedCoupling (I : chebyshev1.SpectralInterval) (N j : ℕ) : ℝ := cachedScalar I N (forwardIndex j 4)

/-- Exactly the four impulse entries consumed by the physical prediction loop. -/
def cachedImpulse (I : chebyshev1.SpectralInterval) (N j k : ℕ) : ℝ :=
  if j<N ∧ k<j ∧ j≤k+4 then cachedScalar I N (forwardIndex j (5+(j-k))) else 0

/-- An output weight retrieved from the descending arithmetic cache. -/
def cachedReadout (I : chebyshev1.SpectralInterval) (N j : ℕ) : ℝ :=
  if j<N then cachedScalar I N (reverseIndex N (N-1-j) 2) else 0

/-- All cached first-kind scalars, including C_N, equal the recursive scalar preparation. -/
theorem cachedC_eq (I : chebyshev1.SpectralInterval) {N j : ℕ} (hN : 2 ≤ N) (hj : j ≤ N) :
    cachedC I N j = preparedC I j := by
  rw [cachedC, cachedScalar_eq I hN (by unfold scalarCells reverseBase forwardIndex; omega),
    scalarValue_forward I hj (by omega)]
  rfl

/-- Every valid cached parity weight is the displayed exact omega. -/
theorem cachedOmega_eq (I : chebyshev1.SpectralInterval) {N j : ℕ} (hN : 2 ≤ N) (hj : j < N) :
    cachedOmega I N j = bezout.Balanced.omega N j := by
  rw [cachedOmega, cachedScalar_eq I hN (by unfold scalarCells reverseBase forwardIndex; omega),
    scalarValue_forward I hj.le (by omega)]
  simp [forwardValue, hj]

/-- Every valid cached normalizer equals the printed Z preparation. -/
theorem cachedZ_eq (I : chebyshev1.SpectralInterval) {N j : ℕ} (hN : 2 ≤ N) (hj : j < N) :
    cachedZ I N j = preparedNormalizer I N j := by
  rw [cachedZ, cachedScalar_eq I hN (by unfold scalarCells reverseBase forwardIndex; omega),
    scalarValue_forward I hj.le (by omega)]
  simp [forwardValue, hj]

/-- Every cached physical impulse consumed by the four-prediction loop is exact. -/
theorem cachedImpulse_eq (I : chebyshev1.SpectralInterval) {N j k : ℕ}
    (hN : 2 ≤ N) (hj : j < N) (hk : k < j) (hband : j ≤ k+4) :
    cachedImpulse I N j k = preparedImpulse I N j k := by
  rw [cachedImpulse, ite_eq_left ⟨hj,hk,hband⟩,
    cachedScalar_eq I hN (by unfold scalarCells reverseBase forwardIndex; omega),
    scalarValue_forward I hj.le (by omega), forwardValue_impulse I hj (by omega) (by omega),
    ite_eq_left (show j-k≤j by omega), show j-(j-k)=k by omega]

/-- Every actual cached readout equals the printed reverse-parity scalar preparation. -/
theorem cachedReadout_eq (I : chebyshev1.SpectralInterval) {N j : ℕ}
    (hN : 2 ≤ N) (hj : j < N) : cachedReadout I N j = preparedReadout I N j := by
  rw [cachedReadout, ite_eq_left hj,
    cachedScalar_eq I hN (by unfold scalarCells reverseIndex reverseBase; omega),
    scalarValue_reverse I (by omega)]
  simp only [reverseValue, Nat.reduceEqDiff, ite_false, show N-1-(N-1-j)=j by omega]

/-- Cached fourth-order coefficients equal the physical loop's exact a_j values. -/
theorem cachedA_eq (I : chebyshev1.SpectralInterval) {N j : ℕ}
    (hN : 2 ≤ N) (hj : j < N) (hj4 : 4 ≤ j) :
    cachedA I N j = bezout.Balanced.recurrenceA I N (j-4) := by
  rw [cachedA, cachedScalar_eq I hN (by unfold scalarCells reverseBase forwardIndex; omega),
    scalarValue_forward I hj.le (by omega)]
  simp [forwardValue, hj, hj4, bezout.Balanced.recurrenceA,
    show j-4+4=j by omega, show j-4+3=j-1 by omega]

/-- Cached fourth-order parity coefficients equal the physical loop's exact c_j values. -/
theorem cachedCoupling_eq (I : chebyshev1.SpectralInterval) {N j : ℕ}
    (hN : 2 ≤ N) (hj : j < N) (hj4 : 4 ≤ j) :
    cachedCoupling I N j = bezout.Balanced.recurrenceC N (j-4) := by
  rw [cachedCoupling, cachedScalar_eq I hN (by unfold scalarCells reverseBase forwardIndex; omega),
    scalarValue_forward I hj.le (by omega)]
  simp [forwardValue, hj, hj4, bezout.Balanced.recurrenceC,
    show j-4+4=j by omega, show j-4+2=j-2 by omega]

/-- The actual scalar cache uses at most eighteen words per horizon call. -/
theorem scalarProgram_cache_le {N : ℕ} (hN : 2 ≤ N) :
    Fintype.card (Fin (scalarCells N)) ≤ 18*N := by
  simpa only [Fintype.card_fin] using scalarCells_le hN

/-- The complete arithmetic-expression description also has linear storage size. -/
theorem scalarProgram_description_le {N : ℕ} (hN : 2 ≤ N) :
    (∑ i : Fin (scalarCells N), ((scalarProgram N).node i).nodeCount) ≤ 2322*N := by
  calc
    _ ≤ ∑ _i : Fin (scalarCells N), (129 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [ScalarExpr.nodeCount_eq]
      have hc := scalarNode_cost N i.val
      change 2 * (scalarNode N i.val).cost + 1 ≤ 129
      omega
    _ = scalarCells N * 129 := by simp
    _ ≤ (18*N)*129 := Nat.mul_le_mul_right 129 (scalarCells_le hN)
    _ = _ := by ring

/-- Cached values and the full finite arithmetic program together require linear storage. -/
theorem scalarProgram_storage_le {N : ℕ} (hN : 2 ≤ N) :
    scalarCells N + (∑ i : Fin (scalarCells N), ((scalarProgram N).node i).nodeCount) ≤ 2340*N := by
  have hc := scalarCells_le hN
  have hp := scalarProgram_description_le hN
  omega

end
end bezout.Algorithms.Balanced
