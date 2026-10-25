import polyak.Farey.Examples.Formulas
import polyak.General.Regions.TongueCriteria

/-! A finite exact phase-floor certificate. Its coverage is a rational
endpoint check; every local sign follows from the existing Bernstein checker.
No numerical acceptance for the example is assumed or asserted here. -/
noncomputable section
namespace polyak.Farey.Examples
open LeanCert.Core LeanCert.Engine Polynomial General
open scoped Polynomial

inductive FloorTest where
  | negativeXi
  | squaredGap
  deriving DecidableEq

def floorPolynomial (p : ℚ[X]) : FloorTest→ℚ[X]
  | .negativeXi => -p
  | .squaredGap => C 3*(1-X^2)-p^2

structure FloorCell (p : ℚ[X]) where
  interval : IntervalRat
  test : FloorTest
  code : Numerics.PolynomialCode (floorPolynomial p test)
  depth : ℕ
  checked : QPoly.bernsteinCheck .strictLower code.code 0 interval depth=true

def intervalCoverCheck (a : ℚ) : List IntervalRat→Bool
  | [] => false
  | I::tail => decide (I.lo≤a) && (decide (1≤I.hi) || intervalCoverCheck I.hi tail)

theorem intervalCoverCheck_covers {a : ℚ} {cells : List IntervalRat}
    (hc : intervalCoverCheck a cells=true) {x : ℝ} (ha : (a:ℝ)≤x) (hx : x≤1) :
    ∃I∈cells,x∈I := by
  induction cells generalizing a with
  | nil => simp only [intervalCoverCheck,Bool.false_eq_true] at hc
  | cons I tail ih =>
    simp only [intervalCoverCheck,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at hc
    by_cases hxi : x≤I.hi
    · exact ⟨I,List.mem_cons_self,le_trans (by exact_mod_cast hc.1) ha,hxi⟩
    · have ht : intervalCoverCheck I.hi tail=true := by
        rcases hc.2 with h | h
        · have hh : (1:ℝ)≤I.hi := by exact_mod_cast h
          exact False.elim (hxi (hx.trans hh))
        · exact h
      obtain ⟨J,hJ,hxJ⟩:=ih ht (le_of_not_ge hxi)
      exact ⟨J,List.mem_cons_of_mem I hJ,hxJ⟩

structure FloorCertificate (p : ℚ[X]) where
  cells : List (FloorCell p)
  covered : intervalCoverCheck (-1) (cells.map FloorCell.interval)=true

theorem FloorCell.alternative {p : ℚ[X]} (C : FloorCell p) {c : ℝ}
    (hc : c∈C.interval) :
    Polynomial.aeval c p<0 ∨ (Polynomial.aeval c p)^2<3*(1-c^2) := by
  have hp:=C.code.positive C.interval C.depth C.checked c hc
  cases ht : C.test with
  | negativeXi =>
    left
    simpa only [ht,floorPolynomial,map_neg,neg_pos] using hp
  | squaredGap =>
    right
    have hh : 0<3*(1-c^2)-(Polynomial.aeval c p)^2 := by
      simpa only [ht,floorPolynomial,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,map_ofNat] using hp
    linarith

theorem FloorCertificate.alternative {p : ℚ[X]} (C : FloorCertificate p)
    {c : ℝ} (hc : c∈Set.Icc (-1:ℝ) 1) :
    Polynomial.aeval c p<0 ∨ (Polynomial.aeval c p)^2<3*(1-c^2) := by
  obtain ⟨I,hI,hcI⟩:=intervalCoverCheck_covers C.covered (by simpa using hc.1) hc.2
  obtain ⟨cell,hcell,he⟩:=List.mem_map.mp hI
  exact cell.alternative (he ▸ hcI)

theorem phase_floor_of_alternative (q : Tuning) {ω : ℝ} (hω : ω∈Set.Ioo 0 Real.pi)
    (h : q.Xi (Real.cos ω)<0 ∨ (q.Xi (Real.cos ω))^2<3*(1-(Real.cos ω)^2)) :
    Real.pi/6<q.angle ω := by
  have hs:=Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hroot : 0≤Real.sqrt 3 := Real.sqrt_nonneg _
  have he : (Real.sqrt 3*Real.sin ω)^2=3*(1-(Real.cos ω)^2) := by
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
    nlinarith [Real.sin_sq_add_cos_sq ω]
  have hb : q.Xi (Real.cos ω)<Real.sqrt 3*Real.sin ω := by
    rcases h with h | h
    · exact lt_of_lt_of_le h (mul_nonneg hroot hs.le)
    · by_contra hn
      have hp:=mul_nonneg hroot hs.le
      nlinarith
  have hφ : Real.pi/6∈Set.Ioo (0:ℝ) Real.pi := ⟨by positivity,by linarith [Real.pi_pos]⟩
  apply (cot_strictAnti (q.angle_mem hω) hφ).mp
  rw [q.cot_angle hω,Real.cos_pi_div_six,Real.sin_pi_div_six]
  have hh : (Real.sqrt 3/2)/(1/2:ℝ)=Real.sqrt 3 := by ring
  rw [hh,div_lt_iff₀ hs]
  exact hb

theorem FloorCertificate.phase_floor {p : ℚ[X]} (C : FloorCertificate p) (q : Tuning)
    (heval : ∀c : ℝ,Polynomial.aeval c p=q.Xi c) :
    ∀ω∈Set.Icc (0:ℝ) Real.pi,Real.pi/6<q.angle ω := by
  intro ω hω
  by_cases hi : ω∈Set.Ioo (0:ℝ) Real.pi
  · apply phase_floor_of_alternative q hi
    simpa only [heval] using C.alternative
      (c:=Real.cos ω) ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  · have he : ω=0 ∨ ω=Real.pi := by
      simp only [Set.mem_Ioo,not_and_or,not_lt] at hi
      rcases hi with h | h
      · exact Or.inl (le_antisymm h hω.1)
      · exact Or.inr (le_antisymm hω.2 h)
    rcases he with rfl | rfl
    · rw [q.angle_zero]
      linarith [Real.pi_pos]
    · rw [q.angle_pi]
      linarith [Real.pi_pos]

theorem thirteen_floor_of_certificate (C : FloorCertificate thirteenXiSource) :
    ∀ω∈Set.Icc (0:ℝ) Real.pi,Real.pi/6<thirteenTuning.angle ω :=
  C.phase_floor thirteenTuning thirteen_Xi_source_exact

end polyak.Farey.Examples
