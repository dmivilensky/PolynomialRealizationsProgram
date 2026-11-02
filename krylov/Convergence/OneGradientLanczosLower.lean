import krylov.Convergence.OneGradientCubicLower
import krylov.Convergence.OneGradientLastCoordinate
import krylov.Convergence.OneGradientSourceDomain

/-!
Article: main_krylov, thm:LB, original actual CG-error lower target.
Use: assemble genuine indistinguishable cubic sources on the actual last
Lanczos axis, normalize their true canonical third budget, and identify
the lower target with the real last CG error. Actual local source
minimizers and positive true Hessians are constructed uniformly.
Source: exact preceding scalar-source, clipping and true critical-point
theorems; this leaf keeps the reference endpoint metric explicit before
transport to each source's true-minimizer metric.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- Normalizing the physical cubic by the true inverse-root last normal
produces exactly the prescribed original diagonal tensor budget and
original last-CG-error lower target. Both genuine twins have actual
local minimizers and positive true Hessians; no parameter regularity
or bounded method output is assumed. Article: main_krylov, thm:LB. -/
theorem oneGradientCubic_lanczos_actual_lower
    (method : OneGradientMethod E) (hmeth : OneGradientSpanRestricted method)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g : E) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=k+1)
    (Mhat δ ρ m R : ℝ) (hMhat : 0<Mhat) (hδ : 0≤δ) (hρ : 0≤ρ) (hρ1 : ρ≤1) (hm : 0<m)
    (hbase : ∀ v,m*‖v‖^2≤ inner ℝ v (cgOperator A v))
    (hcurv : δ≤m/2)
    (hy : let a:=lastLanczosVector A hA g hg hc
      let c:=‖cgOperator (metricRoot A)⁻¹ a‖
      |inner ℝ a (oneGradientQuadraticMinimizer A g)|≤δ/(Mhat/c^3))
    (hsep : let a:=lastLanczosVector A hA g hg hc
      ρ*|inner ℝ a (oneGradientQuadraticMinimizer A g)|≤
        |inner ℝ a (oneGradientQuadraticMinimizer A g)-inner ℝ a (oneGradientLastQuery method (cgOperator A) g k)|)
    (hsmall : let c:=‖cgOperator (metricRoot A)⁻¹ (lastLanczosVector A hA g hg hc)‖
      2*(Mhat/c^3)*(2/m)^2*‖g‖≤1)
    (hball : 2*(2/m)*‖g‖≤R)
    (hpositive : let c:=‖cgOperator (metricRoot A)⁻¹ (lastLanczosVector A hA g hg hc)‖
      (Mhat/c^3)*R≤m/4) :
    let a := lastLanczosVector A hA g hg hc
    let c := ‖cgOperator (metricRoot A)⁻¹ a‖
    let M := Mhat/c^3
    let p := inner ℝ a (oneGradientLastQuery method (cgOperator A) g k)
    let Mp := oneGradientClippedMagnitude M δ p
    let Gp := oneGradientCubicFibreGradient (cgOperator A) g a (-Mp*p/2) Mp
    let Gm := oneGradientCubicFibreGradient (cgOperator A) g a (Mp*p/2) (-Mp)
    let y₀ := inner ℝ a (oneGradientQuadraticMinimizer A g)
    let B := c^2*(M*|y₀|+δ)+M*c^4/4*|y₀| *(M*|y₀|+2*δ)
    Mp*c^3≤Mhat ∧
    oneGradientFunctionRun method Gp 0 (k+1)=oneGradientFunctionRun method Gm 0 (k+1) ∧
    oneGradientFunctionOutput method Gp 0 (k+1)=oneGradientFunctionOutput method Gm 0 (k+1) ∧
    ((Mhat/2)*ρ*‖cgCanonicalError A g k‖^2)/(1+B)≤max
      ‖cgOperator (metricRoot A)⁻¹ (Gp (oneGradientFunctionOutput method Gp 0 (k+1)))‖
      ‖cgOperator (metricRoot A)⁻¹ (Gm (oneGradientFunctionOutput method Gm 0 (k+1)))‖ ∧
    ∀ b∈({-Mp*p/2,Mp*p/2} : Set ℝ),∀ t∈({Mp,-Mp} : Set ℝ),
      ∃ x : E,oneGradientCubicFibreGradient (cgOperator A) g a b t x=0 ∧
        IsMinOn (oneGradientCubicFibreObjective A g a b t) {z | ‖z‖≤R} x ∧
        ‖x‖≤2*(2/m)*‖g‖ ∧
        ‖oneGradientCubicHessian (cgOperator A+b • InnerProductSpace.rankOne ℝ a a) a t x-cgOperator A‖≤
          δ+2*M*(2/m)*‖g‖ ∧
        ∀ v,(m/4)*‖v‖^2≤ inner ℝ v
          (oneGradientCubicHessian (cgOperator A+b • InnerProductSpace.rankOne ℝ a a) a t x v) := by
  let a := lastLanczosVector A hA g hg hc
  let c := ‖cgOperator (metricRoot A)⁻¹ a‖
  let M := Mhat/c^3
  let p := inner ℝ a (oneGradientLastQuery method (cgOperator A) g k)
  let Mp := oneGradientClippedMagnitude M δ p
  have ha : ‖a‖=1 := last_lanczos_unit A hA g hg hc
  have hc0 : 0<c := by
    have hh := oneGradient_last_dual_norm_sq A hA g hg hc
    have hp := cgLength_pos A hA g k (by rw [full_gradient_atom_count A hA g hc];omega)
    change c^2=CG.length (cgOperator A) g k at hh
    have hn : 0≤c := norm_nonneg _
    nlinarith only [hh,hp,hn]
  have hM : 0<M := by dsimp only [M];positivity
  have hpair := oneGradientCubic_clipped_actual_lower method hmeth A hA g a
    (oneGradientQuadraticMinimizer A g) k
    (fun x hx=>(krylov_last_lanczos_hyperplane A hA g hg hc x).mp hx)
    (oneGradientQuadraticMinimizer_critical A hA g) M δ ρ hM hδ hρ hρ1 hy hsep
  have hbnd := oneGradientClippedMagnitude_bounds M δ p hM.le hδ
  have hbudget : Mp*c^3≤Mhat := by
    have hh := mul_le_mul_of_nonneg_right hbnd.2.1 (pow_nonneg hc0.le 3)
    have he : M*c^3=Mhat := by dsimp only [M];field_simp
    exact hh.trans_eq he
  have htarget : (M/2*c)*ρ*|inner ℝ a (oneGradientQuadraticMinimizer A g)|^2=
      Mhat/2*ρ*‖cgCanonicalError A g k‖^2 := by
    have he := oneGradient_last_coordinate_energy A hA g hg hc
    change (inner ℝ a (oneGradientQuadraticMinimizer A g))^2=c^2*‖cgCanonicalError A g k‖^2 at he
    rw [sq_abs,he]
    dsimp only [M]
    field_simp
  refine ⟨hbudget,hpair.2.1,hpair.2.2.1,?_,?_⟩
  · have hl := hpair.2.2.2
    change ((M/2*c)*ρ*|inner ℝ a (oneGradientQuadraticMinimizer A g)|^2)/(1+_)≤_ at hl
    rw [htarget] at hl
    exact hl
  · intro b hb t ht
    have hbp : |b|≤δ := by
      rcases hb with hb|hb
      · rw [hb,neg_mul,neg_div,abs_neg]
        exact hpair.1
      · rw [mem_singleton_iff] at hb
        rw [hb]
        exact hpair.1
    have htb : |t|≤M := by
      have hMp : 0≤Mp := hbnd.1
      rcases ht with ht|ht
      · rw [ht,abs_of_nonneg hMp]
        exact hbnd.2.1
      · rw [mem_singleton_iff] at ht
        rw [ht,abs_neg,abs_of_nonneg hMp]
        exact hbnd.2.1
    obtain ⟨x,hx,hmin,hsize,hrem,hdrift,hform⟩ := oneGradientCubicFibre_uniform_minimum
      A hA g a m δ b t M R hm hM.le hbase hbp (by simpa only [ha,one_pow,mul_one] using hcurv) htb
      (by simpa only [ha,one_pow,mul_one] using hsmall) hball
      (by simpa only [ha,one_pow,mul_one] using hpositive)
    refine ⟨x,hx,hmin,hsize,?_,hform⟩
    simpa only [ha,one_pow,mul_one] using hdrift

end
end krylov.Convergence
