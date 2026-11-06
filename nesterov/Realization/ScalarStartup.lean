import nesterov.Momentum.Execution
import nesterov.Quadratic.Rate
import polyak.Realization.Auxiliary

/-!
Article: Lemma `lem:startup`, choice of the auxiliary scalar quadratic.
Use: one interior curvature has stable from-rest queries that never return to
their initial value. The resulting positive gap holds for every positive time.
-/
namespace nesterov.Realization
noncomputable section
open Polynomial Filter Set
open scoped Topology

def scalarA (β τ h : ℝ) : ℝ[X] := C (-h*(1+τ))*X+C (1+β)
def scalarQ (β τ h : ℝ) : ℝ[X] := C (-h*τ)*X+C β

/-- Actual extrapolated scalar queries, as polynomials in curvature. -/
def queryPolynomial (β τ h : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C (-h*(1+τ))*X+1
  | n+2 => scalarA β τ h*queryPolynomial β τ h (n+1)-
      scalarQ β τ h*queryPolynomial β τ h n

def scalarQuery (β τ h lam : ℝ) (n : ℕ) : ℝ :=
  (queryPolynomial β τ h n).eval lam

theorem affine_degree_leading (a b : ℝ) (ha : a≠0) :
    (C a*X+C b : ℝ[X]).natDegree=1 ∧ (C a*X+C b : ℝ[X]).leadingCoeff=a := by
  constructor
  · rw [natDegree_add_eq_left_of_natDegree_lt (by simp [natDegree_C_mul_X a ha]),
      natDegree_C_mul_X a ha]
  · rw [leadingCoeff_add_of_degree_lt'
      (degree_lt_degree (by simp [natDegree_C_mul_X a ha])),
      leadingCoeff_mul,leadingCoeff_C,leadingCoeff_X,mul_one]

theorem scalarA_degree_leading {β τ h : ℝ} (hh : h≠0) (hτ : 1+τ≠0) :
    (scalarA β τ h).natDegree=1 ∧ (scalarA β τ h).leadingCoeff= -h*(1+τ) :=
  affine_degree_leading _ _ (mul_ne_zero (neg_ne_zero.mpr hh) hτ)

theorem scalarQ_degree_le (β τ h : ℝ) : (scalarQ β τ h).natDegree≤1 := by
  apply (natDegree_add_le _ _).trans
  exact max_le ((natDegree_C_mul_le _ _).trans (by simp)) (by simp)

/-- The exact nonzero leading coefficient excludes every positive-time return
equation at all but finitely many curvatures. -/
theorem queryPolynomial_degree_leading {β τ h : ℝ} (hh : h≠0) (hτ : 1+τ≠0)
    (n : ℕ) :
    (queryPolynomial β τ h n).natDegree=n ∧
      (queryPolynomial β τ h n).leadingCoeff=(-h*(1+τ))^n := by
  have ha := scalarA_degree_leading (β:=β) hh hτ
  have hbase : -h*(1+τ)≠0 := mul_ne_zero (neg_ne_zero.mpr hh) hτ
  suffices H : ∀ n,
      ((queryPolynomial β τ h n).natDegree=n ∧
        (queryPolynomial β τ h n).leadingCoeff=(-h*(1+τ))^n) ∧
      ((queryPolynomial β τ h (n+1)).natDegree=n+1 ∧
        (queryPolynomial β τ h (n+1)).leadingCoeff=(-h*(1+τ))^(n+1)) from (H n).1
  intro n
  induction n with
  | zero =>
    constructor
    · simp [queryPolynomial]
    · simpa [queryPolynomial] using affine_degree_leading (-h*(1+τ)) 1 hbase
  | succ n ih =>
    refine ⟨ih.2,?_⟩
    have ha0 : scalarA β τ h≠0 := by
      intro hz
      have hl := ha.2
      rw [hz,leadingCoeff_zero] at hl
      exact hbase hl.symm
    have hp0 : queryPolynomial β τ h (n+1)≠0 := by
      intro hz
      have hl := ih.2.2
      rw [hz,leadingCoeff_zero] at hl
      exact pow_ne_zero _ hbase hl.symm
    have hfirst : (scalarA β τ h*queryPolynomial β τ h (n+1)).natDegree=n+2 := by
      rw [natDegree_mul ha0 hp0,ha.1,ih.2.1]
      omega
    have hsecond : (scalarQ β τ h*queryPolynomial β τ h n).natDegree≤n+1 := by
      exact natDegree_mul_le.trans (by have := scalarQ_degree_le β τ h; omega)
    constructor
    · change (scalarA β τ h*queryPolynomial β τ h (n+1)-
        scalarQ β τ h*queryPolynomial β τ h n).natDegree=n+1+1
      rw [natDegree_sub_eq_left_of_natDegree_lt (by omega),hfirst]
    · change (scalarA β τ h*queryPolynomial β τ h (n+1)-
        scalarQ β τ h*queryPolynomial β τ h n).leadingCoeff=(-h*(1+τ))^(n+1+1)
      rw [leadingCoeff_sub_of_degree_lt (degree_lt_degree (by omega)),
        leadingCoeff_mul,ha.2,ih.2.2,pow_succ]
      ring

@[simp] theorem scalarQuery_zero (β τ h lam : ℝ) : scalarQuery β τ h lam 0=1 := by
  simp [scalarQuery,queryPolynomial]

@[simp] theorem scalarQuery_one (β τ h lam : ℝ) :
    scalarQuery β τ h lam 1=1-h*lam*(1+τ) := by
  simp [scalarQuery,queryPolynomial]
  ring

theorem scalarQuery_recurrence (β τ h lam : ℝ) (n : ℕ) :
    scalarQuery β τ h lam (n+2)=Quadratic.S β τ h lam*scalarQuery β τ h lam (n+1)-
      Quadratic.Q β τ h lam*scalarQuery β τ h lam n := by
  simp [scalarQuery,queryPolynomial,scalarA,scalarQ,Quadratic.S,Quadratic.Q]
  ring

/-- Polynomial query data agree with the physical source executor from rest. -/
theorem scalarQuery_eq_actual (β τ h lam : ℝ) (n : ℕ) :
    scalarQuery β τ h lam n=Momentum.queryIterate (fun x : ℝ => lam*x) β τ h 1 n := by
  have hrec (k : ℕ) :
      Momentum.queryIterate (fun x : ℝ => lam*x) β τ h 1 (k+2)=
        Quadratic.S β τ h lam*Momentum.queryIterate (fun x : ℝ => lam*x) β τ h 1 (k+1)-
        Quadratic.Q β τ h lam*Momentum.queryIterate (fun x : ℝ => lam*x) β τ h 1 k := by
    rw [Momentum.queryIterate_recurrence]
    simp only [smul_eq_mul,Quadratic.S,Quadratic.Q]
    ring
  have he : ∀ n,scalarQuery β τ h lam n=Momentum.queryIterate (fun x : ℝ => lam*x) β τ h 1 n ∧
      scalarQuery β τ h lam (n+1)=Momentum.queryIterate (fun x : ℝ => lam*x) β τ h 1 (n+1) := by
    intro n
    induction n with
    | zero => simp [Momentum.queryIterate_one]; ring
    | succ n ih =>
      refine ⟨ih.2,?_⟩
      rw [scalarQuery_recurrence,hrec,ih.1,ih.2]
  exact (he n).1

theorem scalarQuery_tendsto_zero {μ L β τ h lam : ℝ}
    (hstable : Quadratic.Stable μ L β τ h) (hlam : lam∈Icc μ L) :
    Tendsto (scalarQuery β τ h lam) atTop (𝓝 0) := by
  obtain ⟨r,s,hr,hs,hrs,hprod⟩ := Quadratic.root_pair (Quadratic.S β τ h lam) (Quadratic.Q β τ h lam)
  have hr' : Quadratic.characteristic β τ h lam r=0 := by rwa [Quadratic.characteristic_eq]
  have hs' : Quadratic.characteristic β τ h lam s=0 := by rwa [Quadratic.characteristic_eq]
  have ht := polyak.Dynamics.recurrence_tendsto_zero_of_roots
    (fun n => (scalarQuery β τ h lam n : ℂ)) r s (hstable lam hlam r hr') (hstable lam hlam s hs')
    (fun n => by rw [hrs,hprod]; exact_mod_cast scalarQuery_recurrence β τ h lam n)
  simpa only [Function.comp_def,Complex.ofReal_re,Complex.zero_re] using
    Complex.continuous_re.continuousAt.tendsto.comp ht

theorem exceptional_countable {β τ h : ℝ} (hh : h≠0) (hτ : 1+τ≠0) :
    {lam : ℝ | ∃ n : ℕ,1≤n ∧ scalarQuery β τ h lam n=1}.Countable := by
  have hfinite (n : ℕ) : {lam : ℝ | 1≤n ∧ scalarQuery β τ h lam n=1}.Countable := by
    by_cases hn : 1≤n
    · have hp : queryPolynomial β τ h n-C 1≠0 := by
        intro hz
        have hd := (queryPolynomial_degree_leading (β:=β) hh hτ n).1
        have he : (queryPolynomial β τ h n-C 1).natDegree=0 := by rw [hz]; rfl
        rw [natDegree_sub_C,hd] at he
        omega
      simpa only [IsRoot,eval_sub,eval_C,sub_eq_zero,scalarQuery,hn,true_and] using
        (finite_setOfPred_isRoot hp).countable
    · simp only [hn,false_and,ofPred_false]
      exact countable_empty
  simpa only [mem_iUnion,mem_ofPred_eq,ofPred_exists] using countable_iUnion hfinite

/-- A single interior curvature and one gap work for the whole infinite startup. -/
theorem exists_scalar_startup {μ L β τ h : ℝ} (hμL : μ<L) (hh : h≠0)
    (hτ : 1+τ≠0) (hstable : Quadratic.Stable μ L β τ h) :
    ∃ lam∈Ioo μ L,Tendsto (scalarQuery β τ h lam) atTop (𝓝 0) ∧
      ∃ η : ℝ,0<η ∧ ∀ n : ℕ,1≤n → η≤(1-scalarQuery β τ h lam n)^2 := by
  obtain ⟨lam,hlam,hno⟩ := (exceptional_countable hh hτ).dense_compl ℝ |>.inter_open_nonempty
    (Ioo μ L) isOpen_Ioo (by exact ⟨(μ+L)/2,by constructor <;> linarith⟩)
  have hlim := scalarQuery_tendsto_zero hstable ⟨hlam.1.le,hlam.2.le⟩
  have hne : ∀ n : ℕ,1≤n → scalarQuery β τ h lam n≠1 := by
    intro n hn he
    exact hno ⟨n,hn,he⟩
  obtain ⟨η,hη,hgap⟩ := polyak.Realization.uniform_return_gap _ hne hlim
  exact ⟨lam,hlam,hlim,η,hη,hgap⟩


/-- The physical auxiliary iterates also decay, not only their queries. -/
theorem scalarIterate_tendsto_zero {μ L β τ h lam : ℝ}
    (hstable : Quadratic.Stable μ L β τ h) (hlam : lam∈Icc μ L) :
    Tendsto (Momentum.iterate (fun x : ℝ=>lam*x) β τ h 1) atTop (𝓝 0) := by
  let P := Momentum.iterate (fun x : ℝ=>lam*x) β τ h 1
  have hrec (k : ℕ) : P (k+2)=Quadratic.S β τ h lam*P (k+1)-Quadratic.Q β τ h lam*P k := by
    dsimp [P]
    rw [Momentum.iterate_recurrence,Momentum.queryIterate_succ]
    simp only [smul_eq_mul,Quadratic.S,Quadratic.Q]
    ring
  obtain ⟨r,s,hr,hs,hrs,hprod⟩ := Quadratic.root_pair (Quadratic.S β τ h lam) (Quadratic.Q β τ h lam)
  have hr' : Quadratic.characteristic β τ h lam r=0 := by rwa [Quadratic.characteristic_eq]
  have hs' : Quadratic.characteristic β τ h lam s=0 := by rwa [Quadratic.characteristic_eq]
  have ht := polyak.Dynamics.recurrence_tendsto_zero_of_roots (fun n=>(P n:ℂ)) r s
    (hstable lam hlam r hr') (hstable lam hlam s hs')
    (fun n=>by rw [hrs,hprod]; exact_mod_cast hrec n)
  simpa only [Function.comp_def,Complex.ofReal_re,Complex.zero_re] using
    Complex.continuous_re.continuousAt.tendsto.comp ht

end
end nesterov.Realization
