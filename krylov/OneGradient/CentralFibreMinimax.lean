import krylov.OneGradient.FibreExact
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(c) and cor:quant(b), central physical fibre.
Use: identify the true central relative-ball endpoints, actual harmonic last
trial and exact arbitrary-method normalized minimax value rho*omega.
Source: the proved physical rank-one relative budget, actual inverse-pivot/CG
length dictionary and the full physical fixed-fibre minimax theorem.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.Methods
variable {n : ℕ}

/-- The genuine central relative-ball endpoints have minimax value rho and
harmonic trial equal to the actual central reference's last CG length.
Use: evaluate the physical information interval without an asymptotic surrogate.
Article: main_krylov, s5:fibre(c) and cor:quant(b).
Proof: the actual positive inverse pivot is the actual last line; both endpoint
reciprocals are h/(1±rho), and direct exact harmonic equioscillation gives the result. -/
theorem central_fibre_parameters
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    {rho : ℝ} (hrho : 0≤rho) (hsmall : rho<1) :
    let h := lastInversePivot A hA g hg hc
    let b0 := lastJacobiPivot A hA g hg hc
    let sigma := b0-h⁻¹
    let blo := b0-rho/h
    let bhi := b0+rho/h
    sigma<blo ∧ blo≤bhi ∧
      intervalMinimaxValue (1/(bhi-sigma)) (1/(blo-sigma))=rho ∧
      harmonicTrial (1/(bhi-sigma)) (1/(blo-sigma))=CG.length (cgOperator A) g n := by
  let h := lastInversePivot A hA g hg hc
  let b0 := lastJacobiPivot A hA g hg hc
  let sigma := b0-h⁻¹
  let blo := b0-rho/h
  let bhi := b0+rho/h
  have hh : 0<h := last_inverse_pivot_positive A hA g hg hc
  have hm : 0<1-rho := sub_pos.mpr hsmall
  have hp : 0<1+rho := by linarith
  have helo : blo-sigma=(1-rho)/h := by dsimp only [blo,sigma];ring
  have hehi : bhi-sigma=(1+rho)/h := by dsimp only [bhi,sigma];ring
  have hleft : sigma<blo := sub_pos.mp (helo ▸ div_pos hm hh)
  have horder : blo≤bhi := by
    have hn := div_nonneg hrho hh.le
    dsimp only [blo,bhi]
    linarith
  have e1 : 1/(bhi-sigma)=h/(1+rho) := by rw [hehi];field_simp
  have e2 : 1/(blo-sigma)=h/(1-rho) := by rw [helo];field_simp
  refine ⟨hleft,horder,?_,?_⟩
  · rw [e1,e2]
    unfold intervalMinimaxValue
    field_simp
    ring
  · rw [e1,e2,← last_inverse_pivot_cg_length A hA g hg hc]
    change harmonicTrial (h/(1+rho)) (h/(1-rho))=h
    unfold harmonicTrial
    field_simp
    ring

/-- The source's uniform relative-ball length-ratio bound is an exact equality
on the original centre's genuine information fibre.
Use: the physical pair of central endpoints attains the uniform ratio, including
zero radius; no limiting reference is needed for the relative-ball case.
Article: main_krylov, s5:fibre(c).
Proof: subtract the actual Schur threshold from both real physical endpoints;
the two positive gaps are (1±rho) divided by the genuine inverse pivot. -/
theorem central_fibre_ratio
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) {rho : ℝ} (hsmall : rho<1) :
    let h := lastInversePivot A hA g hg hc
    let b0 := lastJacobiPivot A hA g hg hc
    let sigma := b0-h⁻¹
    (b0+rho/h-sigma)/(b0-rho/h-sigma)=(1+rho)/(1-rho) := by
  let h := lastInversePivot A hA g hg hc
  let b0 := lastJacobiPivot A hA g hg hc
  have hh : 0<h := last_inverse_pivot_positive A hA g hg hc
  have hm : 0<1-rho := sub_pos.mpr hsmall
  have helo : b0-rho/h-(b0-h⁻¹)=(1-rho)/h := by ring
  have hehi : b0+rho/h-(b0-h⁻¹)=(1+rho)/h := by ring
  dsimp only
  rw [helo,hehi]
  field_simp

/-- On the original centre's information fibre the exact minimax over all
actual methods and every physical matrix in the relative ball is rho*omega.
Use: the central local bound has actual adversarial physical output operators
and an actual attaining one-gradient policy, for zero and positive radii alike.
Article: main_krylov, cor:quant(b), central information fibre.
Proof: the actual physical budget is exactly the derived closed pivot interval;
the complete arbitrary-method fixed-fibre minimum evaluates to rho*omega. -/
theorem central_fibre_exact_minimax
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    {rho omega : ℝ} (hrho : 0≤rho) (hrhosmall : rho<1)
    (homega : 0≤omega) (homegasmall : omega≤1) :
    IsLeast {q : ℝ | ∃ method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+1))),
      OneGradientSpanRestricted method ∧ ∀ b : ℝ,
        relativeBudget A (lanczosCompletion A hA g hg hc b-A)≤rho →
        ∀ B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,B.IsSymm →
          relativeBudget (lanczosCompletion A hA g hg hc b)
            (B-lanczosCompletion A hA g hg hc b)≤omega →
          fibreScenarioError A hA g hg hc method b B≤q}
      (rho*omega) := by
  let h := lastInversePivot A hA g hg hc
  let b0 := lastJacobiPivot A hA g hg hc
  let blo := b0-rho/h
  let bhi := b0+rho/h
  obtain ⟨hlo,horder,hvalue,_⟩ := central_fibre_parameters A hA g hg hc hrho hrhosmall
  have he := fibre_exact_minimax A hA g hg hc blo bhi hlo horder homega homegasmall
  dsimp only at he
  rw [hvalue,mul_comm omega rho] at he
  have hbudget (b : ℝ) : relativeBudget A (lanczosCompletion A hA g hg hc b-A)≤rho ↔ b∈Set.Icc blo bhi :=
    lanczos_completion_central_ball A hA g hg hc rho b
  simpa only [hbudget,Set.mem_ofPred_eq] using he

end
end krylov.OneGradient
