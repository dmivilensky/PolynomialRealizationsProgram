import bezout.Algorithms.BalancedScalarSafety
import bezout.Algorithms.Balanced
import bezout.Algorithms.BalancedProgramCongr

/-!
Article: bezout, Algorithm 2, complete linear-work scalar preparation.
Use: raw mu,L inputs pass through an arithmetic header, the cached raw Balanced
recurrences, and a nine-cell-per-call normalization program. The six-vector
physical loop receives only lookups of these actually computed coefficients.
Proof: each phase is an evaluated scalar DAG. Active-index guards omit absent
quotients, and cache correctness identifies every physical program coefficient.
-/

namespace bezout.Algorithms.Balanced
noncomputable section
open scoped BigOperators

local infixl:65 " +ₑ " => ScalarExpr.add
local infixl:65 " -ₑ " => ScalarExpr.sub
local infixl:70 " *ₑ " => ScalarExpr.mul
local infixl:70 " /ₑ " => ScalarExpr.div

/-- Feed the cached header's eta and Delta to the raw preparation body.
Use: derived spectral parameters are computed from mu,L exactly once. -/
def headerBodyInputs (header : Fin 2 → ℝ) (j : ℕ) : ℝ :=
  if j=0 then header 1 else if j=1 then header 0 else 0

/-- The executed header provides exactly the two raw-body input values. -/
theorem headerBodyInputs_eq (I : chebyshev1.SpectralInterval) :
    headerBodyInputs (intervalHeader.run (intervalInputs I)).values=scalarInputs I := by
  rw [intervalHeader_values]
  funext j
  simp [headerBodyInputs, intervalHeaderValue, scalarInputs]

/-- Read a completed raw-body forward cell as an input to the normalization phase.
Use: these are cached table reads, not repeated scalar preparations. -/
def bodyInput (j f : ℕ) : ScalarExpr := .input (forwardIndex j f)

/-- Nine fixed-size normalization expressions at one physical call.
Fields 0..3 are the prediction weights, 4..7 normalized impulses, and 8 readout.
Inactive future rows are explicitly zero, so no absent normalizer is divided by. -/
def normalizationExpr (N k f : ℕ) : ScalarExpr :=
  if f<4 then
    if k+4<N then
      if f=0 then bodyInput (k+4) 4 *ₑ bodyInput k 2 /ₑ bodyInput (k+4) 2 else
      if f=1 then .constant (-1) *ₑ bodyInput (k+4) 3 *ₑ bodyInput (k+1) 2 /ₑ bodyInput (k+4) 2 else
      if f=2 then (.constant 1 -ₑ bodyInput (k+4) 4) *ₑ bodyInput (k+2) 2 /ₑ bodyInput (k+4) 2 else
        bodyInput (k+4) 3 *ₑ bodyInput (k+3) 2 /ₑ bodyInput (k+4) 2
    else .constant 0
  else if f<8 then
    if k+(f-3)<N then bodyInput (k+(f-3)) (5+(f-3)) /ₑ bodyInput (k+(f-3)) 2 else .constant 0
  else .input (reverseIndex N (N-1-k) 2)

/-- Normalization expressions read only the already completed body input table. -/
theorem normalizationExpr_reads (N k f : ℕ) : (normalizationExpr N k f).reads=∅ := by
  unfold normalizationExpr
  split_ifs <;> rfl

/-- Every physical normalization cell needs at most three real arithmetic operations. -/
theorem normalizationExpr_cost (N k f : ℕ) : (normalizationExpr N k f).cost≤3 := by
  unfold normalizationExpr
  split_ifs <;> norm_num [ScalarExpr.cost, bodyInput]

/-- The actual nine-cell-per-call normalization DAG.
Use: all real divisions needed by the physical loop are included in preparation. -/
def normalizationProgram (N : ℕ) : ScalarProgram (9*N) where
  node s := normalizationExpr N (s.val/9) (s.val%9)
  causal s j hj := by simp only [normalizationExpr_reads, Finset.notMem_empty] at hj

/-- The operation counter of the actual normalization pass is at most 27N. -/
theorem normalizationProgram_cost_le (N : ℕ) (inputs : ℕ → ℝ) :
    ((normalizationProgram N).run inputs).cost≤27*N := by
  rw [ScalarProgram.run_cost]
  calc
    _ ≤ ∑ _ : Fin (9*N), (3 : ℕ) :=
      Finset.sum_le_sum (fun s _ => normalizationExpr_cost N (s.val/9) (s.val%9))
    _ = (9*N)*3 := by simp
    _ = _ := by omega

/-- All three actual cached scalar phase results.
Use: each phase is evaluated once and its stored values are shared by later phases. -/
structure PreparedSetup (N : ℕ) where
  header : ScalarState 2
  body : ScalarState (scalarCells N)
  normalized : ScalarState (9*N)

/-- Complete arithmetic preparation from the original spectral endpoints.
Use: one header run, one raw-body run, one normalization run; no callback reruns a phase. -/
def prepare (I : chebyshev1.SpectralInterval) (N : ℕ) : PreparedSetup N :=
  let header := intervalHeader.run (intervalInputs I)
  let body := (scalarProgram N).run (headerBodyInputs header.values)
  let normalized := (normalizationProgram N).run (ScalarProgram.extend body.values)
  ⟨header,body,normalized⟩

/-- The actual body phase agrees with its separately proved raw-input execution. -/
theorem prepare_body (I : chebyshev1.SpectralInterval) (N : ℕ) :
    (prepare I N).body=(scalarProgram N).run (scalarInputs I) := by
  change (scalarProgram N).run (headerBodyInputs (intervalHeader.run (intervalInputs I)).values)=_
  rw [headerBodyInputs_eq]

/-- The body memory is the same actual cache accessed by all proved raw getters. -/
theorem prepare_bodyMemory (I : chebyshev1.SpectralInterval) (N : ℕ) :
    ScalarProgram.extend (prepare I N).body.values=cachedScalar I N := by
  rw [prepare_body]
  rfl

/-- The third phase normalizes exactly the stored body cache. -/
theorem prepare_normalized (I : chebyshev1.SpectralInterval) (N : ℕ) :
    (prepare I N).normalized=(normalizationProgram N).run (cachedScalar I N) := by
  change (normalizationProgram N).run (ScalarProgram.extend (prepare I N).body.values)=_
  rw [prepare_bodyMemory]

/-- The sum of the three true arithmetic counters is linear in N.
Use: includes the raw interval header and every physical normalization division. -/
theorem prepare_cost_le (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2≤N) :
    (prepare I N).header.cost+(prepare I N).body.cost+(prepare I N).normalized.cost≤1200*N := by
  have hh : (prepare I N).header.cost=3 := intervalHeader_cost _
  have hb : (prepare I N).body.cost≤1152*N := by rw [prepare_body]; exact scalarProgram_work_le I hN
  have hn : (prepare I N).normalized.cost≤27*N := by
    rw [prepare_normalized]
    exact normalizationProgram_cost_le N _
  omega

/-- The stored header, body and normalized cache plus the two raw inputs use linear space. -/
theorem prepare_storage_le {N : ℕ} (hN : 2≤N) :
    Fintype.card (Fin 2)+Fintype.card (Fin (scalarCells N))+Fintype.card (Fin (9*N))+2≤32*N := by
  simp only [Fintype.card_fin]
  unfold scalarCells reverseBase
  omega

/-- A read-free normalization program returns the values of its actual input-only expressions. -/
theorem normalizationProgram_values (N : ℕ) (inputs : ℕ → ℝ) :
    ((normalizationProgram N).run inputs).values=
      fun s => (normalizationExpr N (s.val/9) (s.val%9)).eval inputs (fun _ => 0) := by
  apply ScalarProgram.run_correct_nat _ inputs
    (fun j => (normalizationExpr N (j/9) (j%9)).eval inputs (fun _ => 0))
  intro s
  apply ScalarExpr.eval_congr_reads
  intro j hj
  simp only [normalizationProgram, normalizationExpr_reads, Finset.notMem_empty] at hj

/-- Access the actual normalized cache returned by the complete preparation. -/
def normalizedScalar (I : chebyshev1.SpectralInterval) (N i : ℕ) : ℝ :=
  ScalarProgram.extend (prepare I N).normalized.values i

/-- Every normalized cache address equals its actually evaluated arithmetic expression. -/
theorem normalizedScalar_eq (I : chebyshev1.SpectralInterval) {N k f : ℕ}
    (hk : k<N) (hf : f<9) :
    normalizedScalar I N (9*k+f)=(normalizationExpr N k f).eval (cachedScalar I N) (fun _ => 0) := by
  have hi : 9*k+f<9*N := by omega
  have hd : (9*k+f)/9=k := by omega
  have hm : (9*k+f)%9=f := by omega
  simp only [normalizedScalar, prepare_normalized, normalizationProgram_values,
    ScalarProgram.extend, hi, dite_true, hd, hm]

/-- A normalization input retrieves the actual prepared Z value. -/
theorem bodyInput_Z_eval (I : chebyshev1.SpectralInterval) {N j : ℕ}
    (hN : 2≤N) (hj : j<N) (memory : ℕ → ℝ) :
    (bodyInput j 2).eval (cachedScalar I N) memory=preparedNormalizer I N j :=
  cachedZ_eq I hN hj

/-- A normalization input retrieves the actual prepared fourth-order coefficient. -/
theorem bodyInput_A_eval (I : chebyshev1.SpectralInterval) {N j : ℕ}
    (hN : 2≤N) (hj : j<N) (hj4 : 4≤j) (memory : ℕ → ℝ) :
    (bodyInput j 3).eval (cachedScalar I N) memory=bezout.Balanced.recurrenceA I N (j-4) :=
  cachedA_eq I hN hj hj4

/-- A normalization input retrieves the actual prepared parity coupling. -/
theorem bodyInput_coupling_eval (I : chebyshev1.SpectralInterval) {N j : ℕ}
    (hN : 2≤N) (hj : j<N) (hj4 : 4≤j) (memory : ℕ → ℝ) :
    (bodyInput j 4).eval (cachedScalar I N) memory=bezout.Balanced.recurrenceC N (j-4) :=
  cachedCoupling_eq I hN hj hj4

/-- A normalization input retrieves a raw impulse from the actual four-entry band. -/
theorem bodyInput_impulse_eval (I : chebyshev1.SpectralInterval) {N k d : ℕ}
    (hN : 2≤N) (hd1 : 1≤d) (hd4 : d≤4) (hj : k+d<N) (memory : ℕ → ℝ) :
    (bodyInput (k+d) (5+d)).eval (cachedScalar I N) memory=preparedImpulse I N (k+d) k := by
  have he : cachedImpulse I N (k+d) k=cachedScalar I N (forwardIndex (k+d) (5+d)) := by
    simp [cachedImpulse, hj, show k<k+d by omega, show k+d≤k+4 by omega]
  exact he.symm.trans (cachedImpulse_eq I hN hj (by omega) (by omega))

/-- All four actually normalized prediction weights are the physical program's weights. -/
theorem normalized_weights_eq (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2≤N)
    (k : Fin N) (hk : k.val+4<N) :
    (fun r : Fin 4 => normalizedScalar I N (9*k.val+r.val))=(parameters I N hN).weights k := by
  funext r
  rw [normalizedScalar_eq I k.isLt (by omega : r.val<9)]
  fin_cases r <;>
    simp (disch := omega) [normalizationExpr, parameters, bodyInput_Z_eval I hN,
      bodyInput_A_eval I hN, bodyInput_coupling_eval I hN, hk]

/-- Every actually normalized future impulse equals its physical coefficient. -/
theorem normalized_impulse_eq (I : chebyshev1.SpectralInterval) {N k d : ℕ}
    (hN : 2≤N) (hk : k<N) (hd1 : 1≤d) (hd4 : d≤4) (hj : k+d<N) :
    normalizedScalar I N (9*k+(3+d))=preparedImpulse I N (k+d) k / preparedNormalizer I N (k+d) := by
  rw [normalizedScalar_eq I hk (by omega : 3+d<9)]
  have h4 : ¬3+d<4 := by omega
  have h8 : 3+d<8 := by omega
  simp only [normalizationExpr, h4, h8, ite_false, ite_true,
    show 3+d-3=d by omega, hj, ScalarExpr.eval_div]
  rw [bodyInput_impulse_eval I hN hd1 hd4 hj, bodyInput_Z_eval I hN hj]

/-- The actual normalized readout cell is the scalar coefficient computed by the reverse loop. -/
theorem normalized_readout_eq (I : chebyshev1.SpectralInterval) {N k : ℕ}
    (hN : 2≤N) (hk : k<N) : normalizedScalar I N (9*k+8)=preparedReadout I N k := by
  rw [normalizedScalar_eq I hk (by omega : 8<9)]
  simpa only [normalizationExpr, Nat.reduceLT, ite_false, ScalarExpr.eval_input,
    cachedReadout, hk, ite_true] using cachedReadout_eq I hN hk

/-- Each normalization division has a strictly positive valid-row normalizer.
Use: inactive future coefficients introduce no absent quotient or zero divisor. -/
theorem normalizationExpr_defined (I : chebyshev1.SpectralInterval) {N k f : ℕ}
    (hN : 2≤N) (_hk : k<N) (_hf : f<9) :
    (normalizationExpr N k f).Defined (cachedScalar I N) (fun _ => 0) := by
  have hz (j : ℕ) (hj : j<N) : cachedScalar I N (forwardIndex j 2)≠0 := by
    change cachedZ I N j≠0
    rw [cachedZ_eq I hN hj, preparedNormalizer_eq]
    exact ne_of_gt (bezout.Balanced.normalizer_pos I hN hj)
  unfold normalizationExpr
  split_ifs
  all_goals simp only [ScalarExpr.Defined, bodyInput, ScalarExpr.eval_input, true_and]
  all_goals first | trivial | (apply hz; omega)

/-- Normalization safety holds at the exact prefix where each cache cell executes. -/
theorem normalizationProgram_defined (I : chebyshev1.SpectralInterval) {N : ℕ}
    (hN : 2≤N) (s : Fin (9*N)) :
    ((normalizationProgram N).node s).Defined (ScalarProgram.extend (prepare I N).body.values)
      (ScalarProgram.extend ((normalizationProgram N).runPrefix
        (ScalarProgram.extend (prepare I N).body.values) s.val).values) := by
  rw [prepare_bodyMemory]
  apply (ScalarExpr.defined_congr_reads _ _ (fun _ => 0) _ ?_).mpr
  · exact normalizationExpr_defined I hN (by omega : s.val/9<N) (Nat.mod_lt _ (by omega))
  · intro j hj
    simp only [normalizationProgram, normalizationExpr_reads, Finset.notMem_empty] at hj

/-- Header division safety for the actual complete preparation. -/
theorem prepare_header_defined (I : chebyshev1.SpectralInterval) (s : Fin 2) :
    (intervalHeader.node s).Defined (intervalInputs I)
      (ScalarProgram.extend (intervalHeader.runPrefix (intervalInputs I) s.val).values) :=
  intervalHeader_defined I s

/-- Body division safety with the actually computed header inputs. -/
theorem prepare_body_defined (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2≤N)
    (s : Fin (scalarCells N)) :
    ((scalarProgram N).node s).Defined
      (headerBodyInputs (prepare I N).header.values)
      (ScalarProgram.extend ((scalarProgram N).runPrefix
        (headerBodyInputs (prepare I N).header.values) s.val).values) := by
  change ((scalarProgram N).node s).Defined
    (headerBodyInputs (intervalHeader.run (intervalInputs I)).values) _
  rw [headerBodyInputs_eq]
  exact scalarProgram_defined I hN s

/-- Physical parameters accessed solely by normalized cache lookup.
Use: the physical loop performs no hidden normalization or dense impulse preparation. -/
def parametersFromNormalized (N : ℕ) (memory : ℕ → ℝ) : BalancedParameters N where
  weights k r := memory (9*k.val+r.val)
  impulse j k := if k.val<j ∧ j≤k.val+4 then memory (9*k.val+(3+(j-k.val))) else 0
  readout k := memory (9*k.val+8)

/-- Capture the complete preparation once and retain its normalized coefficient cache. -/
def cachedParameters (I : chebyshev1.SpectralInterval) (N : ℕ) : BalancedParameters N :=
  let result := prepare I N
  parametersFromNormalized N (ScalarProgram.extend result.normalized.values)

/-- Active four-step prediction weights are exactly those of the proved physical loop. -/
theorem cachedParameters_weights (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2≤N)
    (k : Fin N) (hk : k.val+4<N) :
    (cachedParameters I N).weights k=(parameters I N hN).weights k :=
  normalized_weights_eq I hN k hk

/-- Every consumed normalized impulse is exactly the physical scalar coefficient. -/
theorem cachedParameters_impulse (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2≤N)
    (k : Fin N) (d : ℕ) (hd1 : 1≤d) (hd4 : d≤4) (hj : k.val+d<N) :
    (cachedParameters I N).impulse (k.val+d) k=(parameters I N hN).impulse (k.val+d) k := by
  change (if k.val<k.val+d ∧ k.val+d≤k.val+4 then
    normalizedScalar I N (9*k.val+(3+(k.val+d-k.val))) else 0)=_
  simp only [show k.val<k.val+d ∧ k.val+d≤k.val+4 from ⟨by omega, by omega⟩,
    Nat.add_sub_cancel_left]
  exact normalized_impulse_eq I hN k.isLt hd1 hd4 hj

/-- Every consumed readout is exactly the coefficient from the proved reverse accumulators. -/
theorem cachedParameters_readout (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2≤N) :
    (cachedParameters I N).readout=(parameters I N hN).readout := by
  funext k
  exact normalized_readout_eq I hN k.isLt

/-- The six-vector loop instantiated from the actual three-phase RAM preparation. -/
def cachedProgram (I : chebyshev1.SpectralInterval) (N : ℕ) : RegisterProgram 6 N :=
  (cachedParameters I N).program

/-- The actually cache-instantiated loop is the proved physical Balanced program.
Use: inactive future fields may be zero; only coefficients actually consumed by
an active physical instruction need agreement. -/
theorem cachedProgram_eq (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2≤N) :
    cachedProgram I N=program I N hN := by
  apply BalancedParameters.program_eq_of_active
  · intro k hk
    exact cachedParameters_weights I hN k hk
  · intro k d hd1 hd4 hj
    exact cachedParameters_impulse I hN k d hd1 hd4 hj
  · exact cachedParameters_readout I hN

/-- Actual cache preparation and the six-vector loop realize Balanced for every oracle stream. -/
theorem cachedProgram_output_eq_history {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2≤N)
    (oracle : Fin N → E → E) (initial : E) :
    (cachedProgram I N).output oracle initial=
      (bezout.Balanced.history I N hN).oracleOutput initial oracle := by
  rw [cachedProgram_eq I hN]
  exact output_eq_history I N hN oracle initial

/-- Actual cache preparation preserves every physical Balanced query as well. -/
theorem cachedProgram_query_eq_history {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2≤N)
    (oracle : Fin N → E → E) (initial : E) (s : Fin N) :
    (cachedProgram I N).queryAt oracle initial s=
      (bezout.Balanced.history I N hN).oracleQuery initial oracle s := by
  rw [cachedProgram_eq I hN]
  exact query_eq_history I N hN oracle initial s

/-- The actually prepared physical program makes exactly N oracle calls. -/
theorem cachedProgram_oracle_calls {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : chebyshev1.SpectralInterval) (N : ℕ) (oracle : Fin N → E → E) (initial : E) :
    ((cachedProgram I N).run oracle initial).calls=N := RegisterProgram.run_calls _ _ _

/-- The actually prepared physical program retains exactly six vector registers. -/
theorem cachedProgram_vector_slots {E : Type*} (I : chebyshev1.SpectralInterval) (N : ℕ)
    (oracle : Fin N → E → E) (initial : E) : Fintype.card (Fin 6)=6 :=
  RegisterProgram.vector_slots (cachedProgram I N) oracle initial

/-- The entire normalization AST has linearly many operation, input and constant nodes.
Use: cached read visits have constant RAM cost and are included in this tree-size bound. -/
theorem normalizationProgram_description_le (N : ℕ) :
    (∑ s : Fin (9*N), ((normalizationProgram N).node s).nodeCount)≤63*N := by
  calc
    _ ≤ ∑ _ : Fin (9*N), (7 : ℕ) := by
      apply Finset.sum_le_sum
      intro s _
      rw [ScalarExpr.nodeCount_eq]
      have h := normalizationExpr_cost N (s.val/9) (s.val%9)
      change 2*(normalizationExpr N (s.val/9) (s.val%9)).cost+1≤7
      omega
    _ = (9*N)*7 := by simp
    _ = _ := by omega

/-- The three complete scalar program descriptions also have linear storage size. -/
theorem prepare_description_le {N : ℕ} (hN : 2≤N) :
    (∑ s : Fin 2, (intervalHeader.node s).nodeCount)+
    (∑ s : Fin (scalarCells N), ((scalarProgram N).node s).nodeCount)+
    (∑ s : Fin (9*N), ((normalizationProgram N).node s).nodeCount)≤2400*N := by
  have hh : (∑ s : Fin 2, (intervalHeader.node s).nodeCount)=8 := by
    norm_num [intervalHeader, Fin.sum_univ_succ, ScalarExpr.nodeCount]
  have hb := scalarProgram_description_le hN
  have hn := normalizationProgram_description_le N
  omega

end
end bezout.Algorithms.Balanced
