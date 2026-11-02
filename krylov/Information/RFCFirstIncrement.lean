import krylov.Information.KnownBaseMinimaxValue
import krylov.Correction.ScenarioBounds

/-!
Article: main_krylov, thm:C2(c), ordinary RFC sharp known-base witness.
Use: an actual symmetric spectral contraction in the true first/last CG
plane attains the ordinary RFC coefficient one half.
Source: the proved planar reflection norm and genuine one-increment
staircase/fresh-defect geometry on the actual full CG frame.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The concrete actual first/last CG planar reflection attaining the ordinary RFC known-base coefficient.
Use: its scalar multiples obey the source primitive single-increment spectral budget.
Article: main_krylov, thm:C2(c), E₀=ω(eeᵀ+efᵀ+feᵀ−ffᵀ)/√2. -/
def rfcSingleIncrementWitness (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  planarMatrix (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g N)
    (1/Real.sqrt 2) (1/Real.sqrt 2) (-1/Real.sqrt 2)

/-- The actual ordinary RFC planar witness is symmetric, has spectral norm at most one and gives the exact quadratic leading vector for every original budget.
Use: certify the sharp one-half coefficient through the genuine CG flag and original first-increment source geometry, including the zero profile.
Article: main_krylov, thm:C2(c), actual ordinary RFC attaining coefficient.
Proof: the true full CG frame supplies genuine unit orthogonal first and
last directions. The proved planar reflection is a spectral contraction.
Its real hidden diagonal and terminal cross entry both equal 1/√2;
the exact actual one-increment staircase formula gives their product. -/
theorem rfcSingleIncrementWitness_spec (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N) (hcount : referenceAtomCount A hA g=N+1) :
    (rfcSingleIncrementWitness A g).IsSymm ∧ ‖rfcSingleIncrementWitness A g‖≤1 ∧
      ∀ ω : ℝ, staircaseOperator A g (firstIncrement (ω • rfcSingleIncrementWitness A g)) 0 (N+1)
        (freshDefect A g (firstIncrement (ω • rfcSingleIncrementWitness A g)) (N+1))=
          (ω^2/2) • canonicalCGUnitStep A g 0 := by
  -- Derive all real witness pairings from the original full CG reference frame.
  have ho := canonicalCG_frame_of_full_atoms A hA g hcount
  let e := canonicalCGUnitStep A g 0
  let f := canonicalCGUnitStep A g N
  have he : ‖e‖=1 := by simpa only [e,Fin.val_zero] using ho.norm_eq_one (0 : Fin (N+1))
  have hf : ‖f‖=1 := by simpa only [f,Fin.val_last] using ho.norm_eq_one (Fin.last N)
  have hef : inner ℝ e f=0 := by
    simpa only [e,f,Fin.val_zero,Fin.val_last] using ho.inner_eq_zero (i := 0) (j := Fin.last N)
      (by intro h; have hv : (0 : ℕ)=N := congrArg Fin.val h; omega)
  have hfe : inner ℝ f e=0 := (real_inner_comm e f).trans hef
  have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he,one_pow]
  have hff : inner ℝ f f=1 := by rw [real_inner_self_eq_norm_sq,hf,one_pow]
  have hs : (Real.sqrt 2)^2=(2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  refine ⟨planarMatrix_isSymm _ _ _ _ _,?_,?_⟩
  · have hn := planar_spectral_norm_le e f he hf hef (-1/Real.sqrt 2) (1/Real.sqrt 2) (by
      field_simp
      nlinarith)
    simpa only [rfcSingleIncrementWitness,neg_div,neg_neg,e,f,chebyshev1.opNorm] using hn
  · intro ω
    rw [firstIncrement_staircase_fresh A g hN he]
    change ((inner ℝ e (cgOperator (ω • planarMatrix e f (1/Real.sqrt 2) (1/Real.sqrt 2) (-1/Real.sqrt 2)) e))*
      inner ℝ e (cgOperator (ω • planarMatrix e f (1/Real.sqrt 2) (1/Real.sqrt 2) (-1/Real.sqrt 2)) f)) • e=_
    simp only [cgOperator,map_smul,_root_.smul_apply,planarMatrix_action,hee,hff,hef,hfe,
      real_inner_smul_right,inner_add_right,mul_one,mul_zero,add_zero,zero_add]
    congr 1
    field_simp
    nlinarith

end
end krylov.Information
