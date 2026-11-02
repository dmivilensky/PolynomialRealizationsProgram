import bezout.Balanced.Startup
import bezout.History.Oracle

/-!
Article: bezout, Equation `eq:W` and its startup equations.
Use: the literal second-order auxiliary vector recurrence holds for the actual
Balanced queries and answers of every time-dependent oracle, including its
first step. No noiseless or quadratic-oracle assumption is needed.
Proof: expand each raw query in its genuine dense physical impulse row. The
proved row and normalizer recurrences imply the vector fourth-order identity;
its consecutive parity differences give the stated second-order recurrence.
-/

namespace bezout.Balanced
noncomputable section
open scoped BigOperators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The actual raw query Q_s=Z_s y_s, retaining all physical oracle answers. -/
def actualRawQuery (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (initial : E) (oracle : Fin N → E → E) (s : Fin N) : E :=
  normalizer I N s • (history I N hN).oracleQuery initial oracle s

/-- The literal auxiliary vector W_s=(Q_s-Q_(s-2))/omega_s, with W_1=0. -/
def actualAuxiliary (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (initial : E) (oracle : Fin N → E → E) (s : Fin N) : E :=
  if hs : 2≤s.val then (omega N s)⁻¹ •
    (actualRawQuery I N hN initial oracle s-
      actualRawQuery I N hN initial oracle ⟨s.val-2,by omega⟩) else 0

/-- The actual raw query has exactly its dense, strictly causal physical impulse expansion. -/
theorem actualRawQuery_expansion (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (initial : E) (oracle : Fin N → E → E) (s : Fin N) :
    actualRawQuery I N hN initial oracle s=normalizer I N s • initial+
      ∑ k,impulse I N hN s k • (history I N hN).oracleAnswers initial oracle k := by
  rw [actualRawQuery,bezout.History.oracleQuery,smul_sub,Finset.smul_sum,sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [impulse,neg_mul,neg_smul,mul_smul]

/-- A scalar delta impulse selects exactly its corresponding actual physical answer. -/
theorem sum_answer_delta {N : ℕ} (answers : Fin N → E) (j : Fin N) (c : ℝ) :
    (∑ k : Fin N,(if k.val=j.val then c else 0) • answers k)=c • answers j := by
  have he (k : Fin N) : k.val=j.val ↔ k=j := Fin.ext_iff.symm
  simp only [he,ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- The actual raw-query vectors obey the exact forced fourth-order recurrence. -/
theorem actualRawQuery_fourth_order (I : chebyshev1.SpectralInterval) {N s : ℕ}
    (hN : 2≤N) (hs : s+4<N) (initial : E) (oracle : Fin N → E → E) :
    actualRawQuery I N hN initial oracle ⟨s+4,hs⟩=
      recurrenceA I N s • actualRawQuery I N hN initial oracle ⟨s+3,by omega⟩+
      (1-recurrenceC N s) • actualRawQuery I N hN initial oracle ⟨s+2,by omega⟩-
      recurrenceA I N s • actualRawQuery I N hN initial oracle ⟨s+1,by omega⟩+
      recurrenceC N s • actualRawQuery I N hN initial oracle ⟨s,by omega⟩-
      recurrenceB I N s •
        (normalizer I N (s+3) • (history I N hN).oracleAnswers initial oracle ⟨s+3,by omega⟩-
         normalizer I N (s+1) • (history I N hN).oracleAnswers initial oracle ⟨s+1,by omega⟩) := by
  let answers := (history I N hN).oracleAnswers initial oracle
  have hsum : (∑ k : Fin N,impulse I N hN ⟨s+4,hs⟩ k • answers k)=
      recurrenceA I N s • (∑ k,impulse I N hN ⟨s+3,by omega⟩ k • answers k)+
      (1-recurrenceC N s) • (∑ k,impulse I N hN ⟨s+2,by omega⟩ k • answers k)-
      recurrenceA I N s • (∑ k,impulse I N hN ⟨s+1,by omega⟩ k • answers k)+
      recurrenceC N s • (∑ k,impulse I N hN ⟨s,by omega⟩ k • answers k)-
      recurrenceB I N s • (normalizer I N (s+3) • answers ⟨s+3,by omega⟩-
        normalizer I N (s+1) • answers ⟨s+1,by omega⟩) := by
    simp_rw [impulse_recurrence I hN hs]
    simp only [add_smul,sub_smul,mul_smul,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      ← Finset.smul_sum]
    congr 2
    simp only [ite_smul,one_smul,zero_smul]
    have h3 := sum_answer_delta answers ⟨s+3,by omega⟩ (1:ℝ)
    have h1 := sum_answer_delta answers ⟨s+1,by omega⟩ (1:ℝ)
    simp only [ite_smul,one_smul,zero_smul] at h3 h1
    rw [h3,h1]
  have hz := normalizer_fourth_order I hN hs
  change normalizer I N (s+4)=recurrenceA I N s*normalizer I N (s+3)+
    (1-recurrenceC N s)*normalizer I N (s+2)-recurrenceA I N s*normalizer I N (s+1)+
    recurrenceC N s*normalizer I N s at hz
  simp only [actualRawQuery_expansion]
  change _=(recurrenceA I N s • (normalizer I N (s+3) • initial+_)+_)-_+_-_
  rw [hz,hsum]
  module

/-- The exact raw startup query uses the first actual physical oracle answer. -/
theorem actualRawQuery_one (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (initial : E) (oracle : Fin N → E → E) :
    actualRawQuery I N hN initial oracle ⟨1,by omega⟩=I.eta • initial-
      (2/I.delta) • (history I N hN).oracleAnswers initial oracle ⟨0,by omega⟩ := by
  rw [actualRawQuery_expansion,normalizer_one]
  simp_rw [impulse_one]
  rw [sum_answer_delta _ ⟨0,by omega⟩]
  module

/-- The article's initial auxiliary vector W_1 is exactly zero. -/
theorem actualAuxiliary_one (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (initial : E) (oracle : Fin N → E → E) :
    actualAuxiliary I N hN initial oracle ⟨1,by omega⟩=0 := by
  simp [actualAuxiliary]

/-- The initial raw query is precisely the initial physical point. -/
theorem actualRawQuery_zero (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N)
    (initial : E) (oracle : Fin N → E → E) :
    actualRawQuery I N hN initial oracle ⟨0,by omega⟩=initial := by
  rw [actualRawQuery_expansion,normalizer_zero,one_smul]
  have hz (k : Fin N) : impulse I N hN ⟨0,by omega⟩ k=0 :=
    impulse_triangular I N hN _ k (by change (0:ℕ)≤k.val; omega)
  simp only [hz,zero_smul,Finset.sum_const_zero,add_zero]

/-- The exact second raw query uses just the first two actual physical answers. -/
theorem actualRawQuery_two (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2≤N)
    (hs : 2<N) (initial : E) (oracle : Fin N → E → E) :
    actualRawQuery I N hN initial oracle ⟨2,hs⟩=normalizer I N 2 • initial+
      (-4*I.eta*omega N 2/I.delta) •
        ((history I N hN).oracleAnswers initial oracle ⟨0,by omega⟩+
         (history I N hN).oracleAnswers initial oracle ⟨1,by omega⟩) := by
  rw [actualRawQuery_expansion]
  simp_rw [impulse_two I hN hs]
  have hc (k : Fin N) : (if k.val<2 then -4*I.eta*omega N 2/I.delta else 0)=
      (if k.val=0 then -4*I.eta*omega N 2/I.delta else 0)+
      (if k.val=1 then -4*I.eta*omega N 2/I.delta else 0) := by
    by_cases h0 : k.val=0
    · simp [h0]
    · by_cases h1 : k.val=1
      · simp [h1]
      · simp [h0,h1,show ¬k.val<2 by omega]
  simp_rw [hc,add_smul]
  rw [Finset.sum_add_distrib,sum_answer_delta _ ⟨0,by omega⟩,
    sum_answer_delta _ ⟨1,by omega⟩,smul_add]

/-- The literal W_2 startup formula holds for every actual oracle stream. -/
theorem actualAuxiliary_two (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2≤N)
    (hs : 2<N) (initial : E) (oracle : Fin N → E → E) :
    actualAuxiliary I N hN initial oracle ⟨2,hs⟩=(2*(I.eta^2-1)) • initial-
      (4*I.eta/I.delta) •
        ((history I N hN).oracleAnswers initial oracle ⟨0,by omega⟩+
         (history I N hN).oracleAnswers initial oracle ⟨1,by omega⟩) := by
  have hw := ne_of_gt (omega_pos hN hs)
  have hc0 : (omega N 2)⁻¹*(normalizer I N 2-1)=2*(I.eta^2-1) := by
    rw [normalizer_two]
    field_simp
    ring
  have hc1 : (omega N 2)⁻¹*(-4*I.eta*omega N 2/I.delta)= -(4*I.eta/I.delta) := by
    field_simp
  simp only [actualAuxiliary,show (2:ℕ)≤2 by omega,dite_true,Nat.reduceSub]
  rw [actualRawQuery_two I hN hs,actualRawQuery_zero]
  have he (v w : E) : normalizer I N 2 • initial+(-4*I.eta*omega N 2/I.delta) • (v+w)-initial=
      (normalizer I N 2-1) • initial+(-4*I.eta*omega N 2/I.delta) • (v+w) := by module
  rw [he,smul_add,smul_smul,smul_smul,hc0,hc1,neg_smul]
  module

/-- The exact third raw query has the three printed physical startup impulses. -/
theorem actualRawQuery_three (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2≤N)
    (hs : 3<N) (initial : E) (oracle : Fin N → E → E) :
    actualRawQuery I N hN initial oracle ⟨3,hs⟩=normalizer I N 3 • initial+
      startup30 I N • (history I N hN).oracleAnswers initial oracle ⟨0,by omega⟩+
      startup31 I N • (history I N hN).oracleAnswers initial oracle ⟨1,by omega⟩+
      startup32 I N • (history I N hN).oracleAnswers initial oracle ⟨2,by omega⟩ := by
  rw [actualRawQuery_expansion]
  simp_rw [impulse_three I hN hs]
  simp only [mul_ite,mul_one,mul_zero,add_smul,Finset.sum_add_distrib]
  rw [sum_answer_delta _ ⟨0,by omega⟩,sum_answer_delta _ ⟨1,by omega⟩,
    sum_answer_delta _ ⟨2,by omega⟩]
  module

/-- The first step s=2 of Equation W holds for the actual physical oracle answers. -/
theorem actualAuxiliary_first_step (I : chebyshev1.SpectralInterval) {N : ℕ}
    (hN : 2≤N) (hs : 3<N) (initial : E) (oracle : Fin N → E → E) :
    actualAuxiliary I N hN initial oracle ⟨3,hs⟩=
      (2*I.eta) • actualAuxiliary I N hN initial oracle ⟨2,by omega⟩-
      actualAuxiliary I N hN initial oracle ⟨1,by omega⟩-
      (4/(I.delta*omega N 2)) •
        (normalizer I N 2 • (history I N hN).oracleAnswers initial oracle ⟨2,by omega⟩-
         normalizer I N 0 • (history I N hN).oracleAnswers initial oracle ⟨0,by omega⟩) := by
  have hw := ne_of_gt (omega_pos hN hs)
  have hz3 : normalizer I N 3=I.eta+omega N 3*(4*I.eta^3-4*I.eta) :=
    psi_three_eval N I.eta
  have he : actualRawQuery I N hN initial oracle ⟨3,hs⟩-
      actualRawQuery I N hN initial oracle ⟨1,by omega⟩=
      omega N 3 • ((2*I.eta) • actualAuxiliary I N hN initial oracle ⟨2,by omega⟩-
      actualAuxiliary I N hN initial oracle ⟨1,by omega⟩-
      (4/(I.delta*omega N 2)) •
        (normalizer I N 2 • (history I N hN).oracleAnswers initial oracle ⟨2,by omega⟩-
         normalizer I N 0 • (history I N hN).oracleAnswers initial oracle ⟨0,by omega⟩)) := by
    rw [actualRawQuery_three I hN hs,actualRawQuery_one,actualAuxiliary_two,
      actualAuxiliary_one,normalizer_zero,hz3]
    unfold startup30 startup31 startup32
    simp only [div_eq_mul_inv,mul_inv_rev]
    module
  change (omega N 3)⁻¹ • (actualRawQuery I N hN initial oracle ⟨3,hs⟩-
    actualRawQuery I N hN initial oracle ⟨1,by omega⟩)=_
  rw [he,smul_smul,inv_mul_cancel₀ hw,one_smul]

/-- Every subsequent step of Equation W follows from the actual dense physical impulse recurrence. -/
theorem actualAuxiliary_later_step (I : chebyshev1.SpectralInterval) {N s : ℕ}
    (hN : 2≤N) (hs : s+4<N) (initial : E) (oracle : Fin N → E → E) :
    actualAuxiliary I N hN initial oracle ⟨s+4,hs⟩=
      (2*I.eta) • actualAuxiliary I N hN initial oracle ⟨s+3,by omega⟩-
      actualAuxiliary I N hN initial oracle ⟨s+2,by omega⟩-
      (4/(I.delta*omega N (s+3))) •
        (normalizer I N (s+3) • (history I N hN).oracleAnswers initial oracle ⟨s+3,by omega⟩-
         normalizer I N (s+1) • (history I N hN).oracleAnswers initial oracle ⟨s+1,by omega⟩) := by
  have hw := ne_of_gt (omega_pos hN hs)
  have he : actualRawQuery I N hN initial oracle ⟨s+4,hs⟩-
      actualRawQuery I N hN initial oracle ⟨s+2,by omega⟩=
      omega N (s+4) • ((2*I.eta) • actualAuxiliary I N hN initial oracle ⟨s+3,by omega⟩-
      actualAuxiliary I N hN initial oracle ⟨s+2,by omega⟩-
      (4/(I.delta*omega N (s+3))) •
        (normalizer I N (s+3) • (history I N hN).oracleAnswers initial oracle ⟨s+3,by omega⟩-
         normalizer I N (s+1) • (history I N hN).oracleAnswers initial oracle ⟨s+1,by omega⟩)) := by
    rw [actualRawQuery_fourth_order I hN hs]
    simp only [actualAuxiliary,show 2≤s+3 by omega,show 2≤s+2 by omega,
      dite_true,show s+3-2=s+1 by omega,show s+2-2=s by omega]
    unfold recurrenceA recurrenceB recurrenceC
    simp only [div_eq_mul_inv,mul_inv_rev]
    module
  change (omega N (s+4))⁻¹ • (actualRawQuery I N hN initial oracle ⟨s+4,hs⟩-
    actualRawQuery I N hN initial oracle ⟨s+2,by omega⟩)=_
  rw [he,smul_smul,inv_mul_cancel₀ hw,one_smul]

/-- Literal Equation W for every valid s>=2 and every actual time-dependent oracle stream. -/
theorem actualAuxiliary_recurrence (I : chebyshev1.SpectralInterval) {N s : ℕ}
    (hN : 2≤N) (hs2 : 2≤s) (hs : s+1<N) (initial : E) (oracle : Fin N → E → E) :
    actualAuxiliary I N hN initial oracle ⟨s+1,hs⟩=
      (2*I.eta) • actualAuxiliary I N hN initial oracle ⟨s,by omega⟩-
      actualAuxiliary I N hN initial oracle ⟨s-1,by omega⟩-
      (4/(I.delta*omega N s)) •
        (normalizer I N s • (history I N hN).oracleAnswers initial oracle ⟨s,by omega⟩-
         normalizer I N (s-2) • (history I N hN).oracleAnswers initial oracle ⟨s-2,by omega⟩) := by
  by_cases h2 : s=2
  · subst s
    exact actualAuxiliary_first_step I hN hs initial oracle
  · obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le (show 3≤s by omega)
    have heq : s=r+3 := by omega
    simpa only [heq,show r+3+1=r+4 by omega,show r+3-1=r+2 by omega,
      show r+3-2=r+1 by omega] using
      actualAuxiliary_later_step I (s := r) hN (by omega) initial oracle

/-- The second identity of Equation W reconstructs the exact next physical raw query. -/
theorem actualRawQuery_auxiliary_step (I : chebyshev1.SpectralInterval) {N s : ℕ}
    (hN : 2≤N) (hs2 : 2≤s) (hs : s+1<N) (initial : E) (oracle : Fin N → E → E) :
    actualRawQuery I N hN initial oracle ⟨s+1,hs⟩=
      actualRawQuery I N hN initial oracle ⟨s-1,by omega⟩+
      omega N (s+1) • actualAuxiliary I N hN initial oracle ⟨s+1,hs⟩ := by
  have hw := ne_of_gt (omega_pos hN hs)
  simp only [actualAuxiliary,show 2≤s+1 by omega,dite_true,
    show s+1-2=s-1 by omega,smul_smul,mul_inv_cancel₀ hw,one_smul]
  module

end
end bezout.Balanced
