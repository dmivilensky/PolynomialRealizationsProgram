import krylov.Correction.RepeatedRFC
import krylov.Correction.ThreeDirectionReference

/-!
Article: main_krylov, thm:C2(b), the genuine RFC₂ cubic witness.
Use: turn the exact three-direction coefficient into the real method's
terminal asymptotic, rather than leaving only a geometric matrix example.
Source: the actual repeated-RFC expansion and exact homogeneity of the
original finite fresh-defect and staircase sums.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Variation krylov.Envelope
  krylov.Methods krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- Scaling every actual canonical increment scales the genuine fresh vector by the same scalar.
Use: identify the true cubic coefficient of a one-parameter repeated-correction witness.
Article: main_krylov, thm:C2(b), homogeneity of f̂.
Proof: distribute actual matrix scaling through each query action, true
orthogonal projection and finite sum. -/
theorem freshDefect_smul (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (N : ℕ) :
    freshDefect base g (fun i => t • D i) N=t • freshDefect base g D N := by
  simp only [freshDefect,cgOperator,map_smul,_root_.smul_apply,Finset.smul_sum]

/-- Scaling every actual increment and terminal matrix scales the genuine staircase operator.
Use: retain exactly the three powers in the actual RFC₂ leading coefficient.
Article: main_krylov, thm:C2(b), homogeneity of each 𝓛 factor.
Proof: distribute the scalar through both actual compression products and
the finite sum, leaving every true old projector unchanged. -/
theorem staircaseOperator_smul (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (N : ℕ) :
    staircaseOperator base g (fun i => t • D i) (t • F) N=t • staircaseOperator base g D F N := by
  simp only [staircaseOperator,cgOperator,map_smul,mul_smul_comm,smul_mul_assoc,
    Finset.smul_sum,smul_add]

/-- The original actual RFC₂ method has its true cubic leading vector and a quartic remainder on every symmetric increment ray.
Use: combine the attained geometric coefficient with genuine adaptive execution, including both corrections in every prefix iteration.
Article: main_krylov, thm:C2(b), actual third-order response of RFC₂.
Proof: apply the proved repeated-RFC expansion with two corrections and the
original linear increment ray. Both actual staircase factors and the fresh
vector are homogeneous, so their three scalar powers are exactly t³.
-/
theorem rfc_two_cubic_order {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (D : ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hD : ∀ i, (D i).IsSymm) :
    (fun t : ℝ => cgOperator (metricRoot base)⁻¹
      (probedGradient (rfcMethod fullMemory 2) (canonicalFCPath base (fun i => t • D i) 1)
        (fun i => canonicalCorrectionOperator base (fun j => t • D j) 0 i) g (k+1))-
      t^3 • (‖canonicalCGStep base g k‖ • staircaseOperator base g D 0 (k+1)
        (staircaseOperator base g D 0 (k+1) (freshDefect base g D (k+1))))) =O[𝓝 0]
          (fun t => ‖t‖^4) := by
  -- This ray is a genuine primitive operator family for the real repeated method.
  have he := full_repeated_rfc_canonical_order 2 (by omega) base hb g hN hk
    (fun t : ℝ => fun i => t • D i) (fun _ _ => 0)
    (fun _ => analyticAt_id.smul analyticAt_const) (fun _ => analyticAt_const)
    (fun _ => zero_smul _ _) (fun _ => rfl) (fun _ i => (hD i).smul _)
  apply he.congr_left
  intro t
  congr 1
  simp only [chebyshev1.orderedProduct_succ,chebyshev1.orderedProduct_zero,
    mul_one,mul_apply_eq_comp,show (-1 : ℝ)^2=1 by norm_num,one_mul]
  have hs : staircaseOperator base g (fun i => t • D i) 0 (k+1)=
      t • staircaseOperator base g D 0 (k+1) := by
    simpa only [smul_zero] using staircaseOperator_smul base g D 0 t (k+1)
  rw [hs,freshDefect_smul]
  simp only [_root_.smul_apply,map_smul,smul_smul]
  congr 1
  ring

/-- The source three-direction lower coefficient is realized by the original actual RFC₂ terminal gradient for every admissible profile.
Use: certify the cubic lower example through the real complete method, including zero budgets and its full quartic remainder.
Article: main_krylov, thm:C2(b), third-order coefficient at least 2W₀³‖e_last‖_A/(3√3).
Proof: use the concrete genuine-CG matrix family satisfying every primitive
budget and the first two zero increments. The true RFC₂ vector expansion
has quartic remainder. The reverse norm triangle inequality transfers this
to its actual output norm, whose leading vector has the proved attained norm.
-/
theorem rfc_two_cubic_attained {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (hfour : 4≤k+1)
    (ω : ℕ → ℝ) (hω : ∀ i∈range k, 0≤ω i) (hω0 : ω 0=0) (hω1 : ω 1=0) :
    ∃ D : ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ,
      D 0=0 ∧ D 1=0 ∧ (∀ i, (D i).IsSymm) ∧ (∀ i∈range k, ‖D i‖≤ω i) ∧
      (fun t : ℝ => ‖cgOperator (metricRoot base)⁻¹
        (probedGradient (rfcMethod fullMemory 2) (canonicalFCPath base (fun i => t • D i) 1)
          (fun i => canonicalCorrectionOperator base (fun j => t • D j) 0 i) g (k+1))‖-
        ‖t‖^3*(‖cgCanonicalError base g k‖*(2/(3*Real.sqrt 3))*(∑ i∈range k, ω i)^3))
          =O[𝓝 0] (fun t => ‖t‖^4) := by
  -- The same real witness supplies both individual budgets and its actual terminal coefficient.
  let D := threeDirectionIncrements base g (k+1) ω cubicMaximizer (Real.sqrt (1-cubicMaximizer^2))
  have hw := threeDirection_reference_attained base hb g hN hfour ω
    (by simpa only [Nat.add_sub_cancel] using hω) hω0 hω1
  refine ⟨D,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,?_⟩
  let u := fun t : ℝ => cgOperator (metricRoot base)⁻¹
    (probedGradient (rfcMethod fullMemory 2) (canonicalFCPath base (fun i => t • D i) 1)
      (fun i => canonicalCorrectionOperator base (fun j => t • D j) 0 i) g (k+1))
  let c := ‖canonicalCGStep base g k‖ • staircaseOperator base g D 0 (k+1)
    (staircaseOperator base g D 0 (k+1) (freshDefect base g D (k+1)))
  have hr := rfc_two_cubic_order base hb g hN (by omega) D hw.2.2.1
  have hn : (fun t : ℝ => ‖u t‖-‖t^3 • c‖) =O[𝓝 0] (fun t => ‖t‖^4) := by
    have hnorm : (fun t : ℝ => ‖u t‖-‖t^3 • c‖) =O[𝓝 0] (fun t => u t-t^3 • c) :=
      isBigO_of_le _ fun t => by
        simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (u t) (t^3 • c)
    exact hnorm.trans hr
  apply hn.congr_left
  intro t
  have hc : ‖c‖=‖cgCanonicalError base g k‖*(2/(3*Real.sqrt 3))*(∑ i∈range k, ω i)^3 := by
    rw [norm_smul,Real.norm_of_nonneg (norm_nonneg _),← terminal_step_error_norm base hb g hN]
    have hvalue := hw.2.2.2.2
    simp only [Nat.add_sub_cancel] at hvalue
    rw [hvalue]
    ring
  rw [norm_smul,norm_pow,hc]

end
end krylov.Correction
