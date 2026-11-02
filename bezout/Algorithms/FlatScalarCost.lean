import bezout.Algorithms.ScalarProgram
import bezout.Algorithms.Flat

/-!
Article: bezout, Algorithm 1, linear scalar preparation work and storage.
Use: a topologically ordered exact-arithmetic RAM program computes the complete
Flat scalar table, including its cached U values and every physical coefficient.
Proof: local arithmetic equations identify every single-assignment cell with
the proved scalar preparation. The operation counter belongs to the actual
expression evaluator; bounded expressions and a linear cache give linear cost.
-/

namespace bezout.Algorithms.Flat
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Number of cached scalar cells in the explicit preparation program.
Use: includes delta, eta, U_0 through U_N, den, d, both N-entry preparation
loops, both coefficient tables and the two terminal coefficients. -/
def scalarCells (N : ℕ) : ℕ := 5*N+7

/-- Input zero is mu and input one is L; all derived parameters are computed.
Use: eta and delta are not treated as free precomputed arithmetic. -/
def scalarInputs (I : chebyshev1.SpectralInterval) (j : ℕ) : ℝ :=
  if j=0 then I.mu else if j=1 then I.L else 0

/-- One cached second-kind recurrence expression, with the two printed startups.
Use: every predecessor is read from the already computed scalar cache. -/
def scalarUExpr : ℕ → ScalarExpr
  | 0 => .constant 1
  | 1 => .mul (.constant 2) (.read 1)
  | j+2 => .sub (.mul (.mul (.constant 2) (.read 1)) (.read (2+(j+1)))) (.read (2+j))

/-- One running-prefix expression, initialized by the first half source mass.
Use: computes all source prefixes without repeating their sums. -/
def scalarPrefixExpr (N : ℕ) : ℕ → ScalarExpr
  | 0 => .div (.read (2+(N-1))) (.constant 2)
  | m+1 => .add (.read (N+5+m)) (.read (2+(N-2-m)))

/-- One extrapolation coefficient from the cached prefix and equal mass.
Use: the reverse running-sum loop of Algorithm 1. -/
def scalarTauExpr (N s : ℕ) : ScalarExpr :=
  .sub (.div (.sub (.read (N+5+(N-1-s)))
    (.mul (.constant ((N-1-s : ℕ) : ℝ)) (.read (N+4)))) (.read (N+4))) (.constant 1)

/-- One stepsize expression, including its separate startup.
Use: all physical iteration coefficients are computed by the same finite program. -/
def scalarAlphaExpr (s : ℕ) : ScalarExpr :=
  if s=0 then .div (.constant 2) (.add (.input 1) (.input 0))
  else .div (.mul (.constant 4) (.read (2+s))) (.mul (.read 0) (.read (2+(s+1))))

/-- One momentum expression, including zero startup momentum.
Use: prepares the complete coefficient table without an oracle call. -/
def scalarBetaExpr (s : ℕ) : ScalarExpr :=
  if s=0 then .constant 0 else .div (.read (2+(s-1))) (.read (2+(s+1)))

/-- The exact single-assignment instruction at a natural cache address.
The cache order is delta, eta, U, den, d, prefix, tau, alpha, beta, terminal A/B.
Use: no synthesized history coefficient is an input or hidden table lookup. -/
def scalarNode (N k : ℕ) : ScalarExpr :=
  if k=0 then .sub (.input 1) (.input 0)
  else if k=1 then .div (.add (.input 1) (.input 0)) (.read 0)
  else if k<N+3 then scalarUExpr (k-2)
  else if k=N+3 then .sub (.mul (.read 1) (.read (2+(N-1)))) (.read (2+(N-2)))
  else if k=N+4 then .div (.sub (.read (N+3)) (.constant 1))
    (.mul (.mul (.constant 2) (.constant (N:ℝ))) (.sub (.read 1) (.constant 1)))
  else if k<2*N+5 then scalarPrefixExpr N (k-(N+5))
  else if k<3*N+5 then scalarTauExpr N (k-(2*N+5))
  else if k<4*N+5 then scalarAlphaExpr (k-(3*N+5))
  else if k<5*N+5 then scalarBetaExpr (k-(4*N+5))
  else if k=5*N+5 then .div (.read (2+(N-2))) (.read (N+3))
  else .div (.mul (.constant 2) (.read (2+(N-1)))) (.mul (.read 0) (.read (N+3)))

/-- Expected values of all cells, stated using the already verified preparation.
Use: a specification for the actual topological execution, not its evaluator. -/
def scalarValue (I : chebyshev1.SpectralInterval) (N k : ℕ) : ℝ :=
  if k=0 then I.delta
  else if k=1 then I.eta
  else if k<N+3 then preparedU I (k-2)
  else if k=N+3 then preparedDen I N
  else if k=N+4 then preparedMass I N
  else if k<2*N+5 then preparedPrefix I N (k-(N+5))
  else if k<3*N+5 then preparedTau I N (k-(2*N+5))
  else if k<4*N+5 then bezout.Flat.alpha I (k-(3*N+5))
  else if k<5*N+5 then bezout.Flat.beta I (k-(4*N+5))
  else if k=5*N+5 then bezout.Flat.terminalA I N
  else bezout.Flat.terminalB I N

/-- The cache's first cell computes delta. -/
@[simp] theorem scalarValue_delta (I : chebyshev1.SpectralInterval) (N : ℕ) :
    scalarValue I N 0 = I.delta := by simp [scalarValue]

/-- The cache's second cell computes eta. -/
@[simp] theorem scalarValue_eta (I : chebyshev1.SpectralInterval) (N : ℕ) :
    scalarValue I N 1 = I.eta := by simp [scalarValue]

/-- Cached U addresses have their prescribed recurrence values. -/
theorem scalarValue_U (I : chebyshev1.SpectralInterval) (N j : ℕ) (hj : j≤N) :
    scalarValue I N (2+j) = preparedU I j := by
  unfold scalarValue
  split_ifs <;> first | contradiction | omega | rfl | (congr 1; omega)

/-- The cached terminal denominator has its prescribed preparation value. -/
theorem scalarValue_den (I : chebyshev1.SpectralInterval) (N : ℕ) :
    scalarValue I N (N+3) = preparedDen I N := by
  unfold scalarValue
  split_ifs <;> first | contradiction | omega | rfl

/-- The cached common mass has its prescribed preparation value. -/
theorem scalarValue_mass (I : chebyshev1.SpectralInterval) (N : ℕ) :
    scalarValue I N (N+4) = preparedMass I N := by
  unfold scalarValue
  split_ifs <;> first | contradiction | omega | rfl

/-- Cached running-prefix addresses have their prescribed preparation values. -/
theorem scalarValue_prefix (I : chebyshev1.SpectralInterval) (N m : ℕ) (hm : m<N) :
    scalarValue I N (N+5+m) = preparedPrefix I N m := by
  unfold scalarValue
  split_ifs <;> first | contradiction | omega | rfl | (congr 1; omega)

/-- Cached extrapolation addresses have their prescribed preparation values. -/
theorem scalarValue_tau (I : chebyshev1.SpectralInterval) (N s : ℕ) (hs : s<N) :
    scalarValue I N (2*N+5+s) = preparedTau I N s := by
  unfold scalarValue
  split_ifs <;> first | contradiction | omega | rfl | (congr 1; omega)

/-- Cached stepsize addresses have their prescribed physical values. -/
theorem scalarValue_alpha (I : chebyshev1.SpectralInterval) (N s : ℕ) (hs : s<N) :
    scalarValue I N (3*N+5+s) = bezout.Flat.alpha I s := by
  unfold scalarValue
  split_ifs <;> first | contradiction | omega | rfl | (congr 1; omega)

/-- Cached momentum addresses have their prescribed physical values. -/
theorem scalarValue_beta (I : chebyshev1.SpectralInterval) (N s : ℕ) (hs : s<N) :
    scalarValue I N (4*N+5+s) = bezout.Flat.beta I s := by
  unfold scalarValue
  split_ifs <;> first | contradiction | omega | rfl | (congr 1; omega)

/-- The cached terminal momentum has its prescribed physical value. -/
theorem scalarValue_terminalA (I : chebyshev1.SpectralInterval) (N : ℕ) :
    scalarValue I N (5*N+5) = bezout.Flat.terminalA I N := by
  unfold scalarValue
  split_ifs <;> first | contradiction | omega | rfl

/-- The cached terminal stepsize has its prescribed physical value. -/
theorem scalarValue_terminalB (I : chebyshev1.SpectralInterval) (N : ℕ) :
    scalarValue I N (5*N+6) = bezout.Flat.terminalB I N := by
  unfold scalarValue
  split_ifs <;> first | contradiction | omega | rfl

/-- The cached U expression reads only earlier cells. -/
theorem scalarUExpr_causal (j k : ℕ) (hk : k∈(scalarUExpr j).reads) : k<2+j := by
  match j with
  | 0 => simp [scalarUExpr, ScalarExpr.reads] at hk
  | 1 => simp [scalarUExpr, ScalarExpr.reads] at hk; omega
  | j+2 => simp [scalarUExpr, ScalarExpr.reads] at hk; omega

/-- Every actual Flat preparation read points to a previously computed cache cell.
Use: the exact-arithmetic program is a DAG with no recursive recomputation. -/
theorem scalarNode_causal (N : ℕ) (hN : 2≤N) (k j : ℕ)
    (hk : k<scalarCells N) (hj : j∈(scalarNode N k).reads) : j<k := by
  unfold scalarNode at hj
  split_ifs at hj with h0 h1 hU hden hmass hp ht ha hb hA
  · simp [ScalarExpr.reads] at hj
  · simp [ScalarExpr.reads] at hj; omega
  · have h := scalarUExpr_causal (k-2) j hj
    omega
  · simp [ScalarExpr.reads] at hj; omega
  · simp [ScalarExpr.reads] at hj; omega
  · unfold scalarPrefixExpr at hj
    split at hj <;> simp_all [ScalarExpr.reads] <;> omega
  · simp [scalarTauExpr, ScalarExpr.reads] at hj
    omega
  · unfold scalarAlphaExpr at hj
    split_ifs at hj <;> simp_all [ScalarExpr.reads]
    all_goals omega
  · unfold scalarBetaExpr at hj
    split_ifs at hj <;> simp_all [ScalarExpr.reads]
    all_goals omega
  · simp [ScalarExpr.reads] at hj; omega
  · simp [ScalarExpr.reads] at hj; unfold scalarCells at hk; omega

/-- The actual cached scalar straight-line program for Flat preparation.
Use: its interpreter performs one topological evaluation per cache cell. -/
def scalarProgram (N : ℕ) (hN : 2≤N) : ScalarProgram (scalarCells N) where
  node s := scalarNode N s.val
  causal s j hj := scalarNode_causal N hN s.val j s.isLt hj

/-- Each actual instruction evaluates to its separately specified scalar value.
Use: the local equations for topological cached-execution correctness. -/
theorem scalarNode_eval (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (k : ℕ) (_hk : k<scalarCells N) :
    (scalarNode N k).eval (scalarInputs I) (scalarValue I N) = scalarValue I N k := by
  conv_rhs => unfold scalarValue
  unfold scalarNode
  split_ifs with h0 h1 hU hden hmass hp ht ha hb hA
  · simp [scalarInputs, chebyshev1.SpectralInterval.delta]
  · simp [scalarInputs, chebyshev1.SpectralInterval.eta]
  · have hj : k-2≤N := by omega
    generalize hindex : k-2=j at *
    match j with
    | 0 => simp [scalarUExpr, preparedU]
    | 1 => simp [scalarUExpr, preparedU]
    | j+2 =>
      simp only [scalarUExpr, ScalarExpr.eval_sub, ScalarExpr.eval_mul,
        ScalarExpr.eval_constant, ScalarExpr.eval_read, scalarValue_eta,
        scalarValue_U I N (j+1) (by omega), scalarValue_U I N j (by omega), preparedU]
  · simp only [ScalarExpr.eval_sub, ScalarExpr.eval_mul, ScalarExpr.eval_read,
      scalarValue_eta, scalarValue_U I N (N-1) (by omega),
      scalarValue_U I N (N-2) (by omega), preparedDen]
  · simp only [ScalarExpr.eval_div, ScalarExpr.eval_sub, ScalarExpr.eval_mul,
      ScalarExpr.eval_read, ScalarExpr.eval_constant, scalarValue_den, scalarValue_eta,
      preparedMass]
  · have hm : k-(N+5)<N := by omega
    generalize hindex : k-(N+5)=m at *
    match m with
    | 0 =>
      simp only [scalarPrefixExpr, ScalarExpr.eval_div, ScalarExpr.eval_read,
        ScalarExpr.eval_constant, scalarValue_U I N (N-1) (by omega), preparedPrefix]
    | m+1 =>
      simp only [scalarPrefixExpr, ScalarExpr.eval_add, ScalarExpr.eval_read,
        scalarValue_prefix I N m (by omega), scalarValue_U I N (N-2-m) (by omega), preparedPrefix]
  · have hs : k-(2*N+5)<N := by omega
    let s := k-(2*N+5)
    change (scalarTauExpr N s).eval (scalarInputs I) (scalarValue I N) = preparedTau I N s
    simp only [scalarTauExpr, ScalarExpr.eval_sub, ScalarExpr.eval_div, ScalarExpr.eval_mul,
      ScalarExpr.eval_constant, ScalarExpr.eval_read, scalarValue_mass,
      scalarValue_prefix I N (N-1-s) (by omega), preparedTau]
  · have hs : k-(3*N+5)<N := by omega
    let s := k-(3*N+5)
    change (scalarAlphaExpr s).eval (scalarInputs I) (scalarValue I N) = bezout.Flat.alpha I s
    unfold scalarAlphaExpr bezout.Flat.alpha
    split_ifs
    · simp [scalarInputs]
    · simp only [ScalarExpr.eval_div, ScalarExpr.eval_mul, ScalarExpr.eval_constant,
        ScalarExpr.eval_read, scalarValue_delta, scalarValue_U I N s (by omega),
        scalarValue_U I N (s+1) (by omega), preparedU_eq]
  · have hs : k-(4*N+5)<N := by omega
    let s := k-(4*N+5)
    change (scalarBetaExpr s).eval (scalarInputs I) (scalarValue I N) = bezout.Flat.beta I s
    unfold scalarBetaExpr bezout.Flat.beta
    split_ifs
    · simp
    · simp only [ScalarExpr.eval_div, ScalarExpr.eval_read,
        scalarValue_U I N (s-1) (by omega), scalarValue_U I N (s+1) (by omega), preparedU_eq]
  · simp only [ScalarExpr.eval_div, ScalarExpr.eval_read,
      scalarValue_U I N (N-2) (by omega), scalarValue_den,
      preparedU_eq, preparedDen_eq I N hN, bezout.Flat.terminalA]
  · simp only [ScalarExpr.eval_div, ScalarExpr.eval_mul, ScalarExpr.eval_constant,
      ScalarExpr.eval_read, scalarValue_delta, scalarValue_U I N (N-1) (by omega),
      scalarValue_den, preparedU_eq, preparedDen_eq I N hN, bezout.Flat.terminalB]

/-- The actual single-pass scalar RAM returns the entire prescribed Flat table.
Use: every cached coefficient is computed once from earlier cells. -/
theorem scalarProgram_correct (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N) :
    ((scalarProgram N hN).run (scalarInputs I)).values = fun s => scalarValue I N s.val := by
  apply ScalarProgram.run_correct_nat
  intro s
  exact scalarNode_eval I N hN s.val s.isLt

/-- Each cached U expression uses at most three arithmetic operations. -/
theorem scalarUExpr_cost (j : ℕ) : (scalarUExpr j).cost≤3 := by
  match j with
  | 0 => norm_num [scalarUExpr, ScalarExpr.cost]
  | 1 => norm_num [scalarUExpr, ScalarExpr.cost]
  | j+2 => norm_num [scalarUExpr, ScalarExpr.cost]

/-- A running-prefix expression uses at most one arithmetic operation. -/
theorem scalarPrefixExpr_cost (N m : ℕ) : (scalarPrefixExpr N m).cost≤5 := by
  cases m <;> norm_num [scalarPrefixExpr, ScalarExpr.cost]

/-- An extrapolation expression uses a fixed number of arithmetic operations. -/
theorem scalarTauExpr_cost (N s : ℕ) : (scalarTauExpr N s).cost≤5 := by
  norm_num [scalarTauExpr, ScalarExpr.cost]

/-- A stepsize expression uses a fixed number of arithmetic operations. -/
theorem scalarAlphaExpr_cost (s : ℕ) : (scalarAlphaExpr s).cost≤5 := by
  unfold scalarAlphaExpr
  split_ifs <;> norm_num [ScalarExpr.cost]

/-- A momentum expression uses a fixed number of arithmetic operations. -/
theorem scalarBetaExpr_cost (s : ℕ) : (scalarBetaExpr s).cost≤5 := by
  unfold scalarBetaExpr
  split_ifs <;> norm_num [ScalarExpr.cost]

/-- Every actual node contains at most five scalar arithmetic operations.
Use: bounds the true evaluator counter from a fixed-size instruction AST. -/
theorem scalarNode_cost (N k : ℕ) : (scalarNode N k).cost≤5 := by
  unfold scalarNode
  split_ifs
  all_goals first
    | exact (scalarUExpr_cost _).trans (by omega)
    | exact scalarPrefixExpr_cost _ _
    | exact scalarTauExpr_cost _ _
    | exact scalarAlphaExpr_cost _
    | exact scalarBetaExpr_cost _
    | norm_num [ScalarExpr.cost]

/-- The actual arithmetic counter of scalar preparation grows linearly in N.
Use: the conventional exact-arithmetic RAM work bound with cached lookups. -/
theorem scalarProgram_cost_le (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N) :
    ((scalarProgram N hN).run (scalarInputs I)).cost≤64*N := by
  rw [ScalarProgram.run_cost]
  calc
    _ ≤ ∑ _ : Fin (scalarCells N), 5 := Finset.sum_le_sum (fun s _ => scalarNode_cost N s.val)
    _ = (scalarCells N)*5 := by simp
    _ ≤ 64*N := by unfold scalarCells; omega

/-- The actual cache contains linearly many stored scalar values.
Use: inputs occupy two further scalar cells; neither cache nor inputs hide a
quadratic impulse table or a repeated recursive preparation. -/
theorem scalarProgram_storage_le (N : ℕ) (hN : 2≤N) :
    Fintype.card (Fin (scalarCells N)) + 2≤64*N := by
  rw [Fintype.card_fin]
  unfold scalarCells
  omega

/-- Cached U expressions perform no division. -/
theorem scalarUExpr_defined (inputs memory : ℕ → ℝ) (j : ℕ) :
    (scalarUExpr j).Defined inputs memory := by
  match j with
  | 0 => trivial
  | 1 => trivial
  | j+2 => trivial

/-- Every division in the specified Flat DAG has a nonzero denominator.
Use: rules out total-real-division artifacts at every boundary and startup. -/
theorem scalarNode_defined (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (k : ℕ) (_hk : k<scalarCells N) :
    (scalarNode N k).Defined (scalarInputs I) (scalarValue I N) := by
  have hdelta : I.delta≠0 := ne_of_gt I.delta_pos
  have heta : I.eta-1≠0 := ne_of_gt (sub_pos.mpr I.eta_gt_one)
  have hden : preparedDen I N≠0 := by rw [preparedDen_eq I N hN]; exact I.den_ne N
  have hmass : preparedMass I N≠0 := by
    rw [preparedMass_eq I N hN]
    exact ne_of_gt (bezout.Flat.unitMass_pos I N (by omega))
  have hu (j : ℕ) : preparedU I j≠0 := by rw [preparedU_eq]; exact ne_of_gt (bezout.Flat.u_pos I j)
  unfold scalarNode
  split_ifs with h0 h1 hU hd hm hp ht ha hb hA
  · trivial
  · simpa [ScalarExpr.Defined] using hdelta
  · exact scalarUExpr_defined _ _ _
  · trivial
  · simp only [ScalarExpr.Defined, ScalarExpr.eval_mul, ScalarExpr.eval_sub,
      ScalarExpr.eval_constant, ScalarExpr.eval_read, scalarValue_eta, true_and]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast (by omega : N≠0))) heta
  · generalize hindex : k-(N+5)=m
    cases m <;> norm_num [scalarPrefixExpr, ScalarExpr.Defined]
  · simpa [scalarTauExpr, ScalarExpr.Defined, scalarValue_mass] using hmass
  · have hs : k-(3*N+5)<N := by omega
    let s := k-(3*N+5)
    change (scalarAlphaExpr s).Defined _ _
    unfold scalarAlphaExpr
    split_ifs
    · simp only [ScalarExpr.Defined, ScalarExpr.eval_add, ScalarExpr.eval_input,
        scalarInputs, ite_true, one_ne_zero, ite_false, true_and]
      exact ne_of_gt (by linarith [I.mu_pos, I.mu_lt_L])
    · simp only [ScalarExpr.Defined, ScalarExpr.eval_mul, ScalarExpr.eval_read,
        scalarValue_delta, scalarValue_U I N (s+1) (by omega), true_and]
      exact mul_ne_zero hdelta (hu _)
  · have hs : k-(4*N+5)<N := by omega
    let s := k-(4*N+5)
    change (scalarBetaExpr s).Defined _ _
    unfold scalarBetaExpr
    split_ifs
    · trivial
    · simpa only [ScalarExpr.Defined, ScalarExpr.eval_read,
        scalarValue_U I N (s+1) (by omega), true_and] using hu (s+1)
  · simpa [ScalarExpr.Defined, scalarValue_den] using hden
  · simpa [ScalarExpr.Defined, scalarValue_delta, scalarValue_den] using mul_ne_zero hdelta hden

/-- Division validity holds in the actual cached prefix at the instant each
instruction executes, not only in the mathematical specification table. -/
theorem scalarProgram_defined (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (s : Fin (scalarCells N)) :
    ((scalarProgram N hN).node s).Defined (scalarInputs I)
      (ScalarProgram.extend ((scalarProgram N hN).runPrefix (scalarInputs I) s.val).values) := by
  apply ScalarProgram.runPrefix_defined_nat _ _ (scalarValue I N)
  · intro j
    exact scalarNode_eval I N hN j.val j.isLt
  · intro j
    exact scalarNode_defined I N hN j.val j.isLt

/-- Natural-address access to the actual completed scalar cache. -/
def scalarResult (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N) : ℕ → ℝ :=
  ScalarProgram.extend ((scalarProgram N hN).run (scalarInputs I)).values

/-- Every actual cache result equals its verified preparation specification. -/
theorem scalarResult_correct (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (j : ℕ) (hj : j<scalarCells N) : scalarResult I N hN j=scalarValue I N j := by
  rw [scalarResult, scalarProgram_correct]
  simp only [ScalarProgram.extend, hj, dite_true]

/-- The actual cache returns each physical extrapolation coefficient. -/
theorem scalarResult_tau (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (s : Fin N) : scalarResult I N hN (2*N+5+s.val)=bezout.Flat.tau I N s := by
  rw [scalarResult_correct I N hN _ (by unfold scalarCells; omega),
    scalarValue_tau I N s.val s.isLt, preparedTau_eq I N hN s]

/-- The actual cache returns each physical stepsize coefficient. -/
theorem scalarResult_alpha (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (s : Fin N) : scalarResult I N hN (3*N+5+s.val)=bezout.Flat.alpha I s := by
  rw [scalarResult_correct I N hN _ (by unfold scalarCells; omega), scalarValue_alpha I N s.val s.isLt]

/-- The actual cache returns each physical momentum coefficient. -/
theorem scalarResult_beta (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (s : Fin N) : scalarResult I N hN (4*N+5+s.val)=bezout.Flat.beta I s := by
  rw [scalarResult_correct I N hN _ (by unfold scalarCells; omega), scalarValue_beta I N s.val s.isLt]

/-- The actual cache returns the terminal momentum coefficient. -/
theorem scalarResult_terminalA (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N) :
    scalarResult I N hN (5*N+5)=bezout.Flat.terminalA I N := by
  rw [scalarResult_correct I N hN _ (by unfold scalarCells; omega), scalarValue_terminalA]

/-- The actual cache returns the terminal gradient coefficient. -/
theorem scalarResult_terminalB (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N) :
    scalarResult I N hN (5*N+6)=bezout.Flat.terminalB I N := by
  rw [scalarResult_correct I N hN _ (by unfold scalarCells; omega), scalarValue_terminalB]

/-- Read the physical Flat coefficient table from an already computed cache.
Use: these accessors perform cached lookups and do not rerun scalar preparation. -/
def parametersFromCache (N : ℕ) (memory : ℕ → ℝ) : FlatParameters N where
  tau s := memory (2*N+5+s.val)
  alpha s := memory (3*N+5+s.val)
  beta s := memory (4*N+5+s.val)
  terminalA := memory (5*N+5)
  terminalB := memory (5*N+6)

/-- Physical parameters read solely from one actual completed RAM execution.
Use: the prepared table is computed once and captured by the physical accessors. -/
def cachedParameters (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N) : FlatParameters N :=
  let result := (scalarProgram N hN).run (scalarInputs I)
  parametersFromCache N (ScalarProgram.extend result.values)

/-- The cache supplies exactly every scalar of the proved physical Flat program. -/
theorem cachedParameters_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N) :
    cachedParameters I N hN=parameters I N := by
  unfold cachedParameters parametersFromCache parameters
  change FlatParameters.mk _ _ _ _ _=FlatParameters.mk _ _ _ _ _
  congr 1
  · funext s
    exact scalarResult_tau I N hN s
  · funext s
    exact scalarResult_alpha I N hN s
  · funext s
    exact scalarResult_beta I N hN s
  · exact scalarResult_terminalA I N hN
  · exact scalarResult_terminalB I N hN

/-- The four-vector physical program instantiated by the actually evaluated cache. -/
def cachedProgram (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N) : RegisterProgram 4 N :=
  (cachedParameters I N hN).program

/-- Linear-work scalar preparation produces the exact proved four-vector Flat program. -/
theorem cachedProgram_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N) :
    cachedProgram I N hN=program I N := by rw [cachedProgram, cachedParameters_eq]; rfl

/-- The cache-instantiated physical program realizes Flat on every actual oracle stream. -/
theorem cachedProgram_output_eq_history {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (oracle : Fin N → E → E) (initial : E) :
    (cachedProgram I N hN).output oracle initial =
      (bezout.Flat.history I N hN).oracleOutput initial oracle := by
  rw [cachedProgram_eq]
  exact output_eq_history I N hN oracle initial

end
end bezout.Algorithms.Flat
