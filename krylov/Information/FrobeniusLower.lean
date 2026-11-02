import krylov.Information.FrobeniusAdmissibility
import krylov.Information.KnownBaseRadius

/-!
Article: main_krylov, thm:C2(a), genuine sharp Frobenius minimax lower pair.
Use: every original profile has actual admissible physical witnesses with
exactly fixed known base forcing K(W,w)/√2 up to a uniform cubic loss.
Source: the true symmetric planar Frobenius energy, genuine scalar
maximizer and complete actual one-query information-fibre execution.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability
open scoped BigOperators MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
/-- Every original Frobenius profile has an explicit admissible fixed-base signed pair forcing K(W,w)/√2 with a common cubic loss for every genuine source method.
Use: this is the sharp actual information-minimax lower obstruction, already on scenarios whose base is exactly known.
Article: main_krylov, thm:C2(a), genuine all-profile known-base Frobenius lower bound.
Proof: use the actual first and last CG unit steps and the maximizing
spectral coordinates, dividing only the cross coordinate by √2. Exact
Frobenius energy and the physical root bridge discharge every primitive
budget. The actual common-data output radius then has quadratic coefficient
K/√2 and a uniform two-cubic loss; no reference variation is used.
-/
theorem admissible_frobenius_normalized_lower {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) (h1 : OneCorrectionMethod m)
    (ω : ℕ → ℝ) (w τ r : ℝ) (hω : ∀ i<N, 0≤ω i) (hw : 0≤w) (hτ : 0≤τ) (hr : 0≤r)
    (hs : (∑ i∈range N, ω i)+w≤(1/2 : ℝ)) :
    let W := ∑ i∈range N, ω i
    let a := maximizingCross W w/Real.sqrt 2
    let γ := maximizingComplement W w
    let S := fun σ => (knownBasePlanarScenario (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g N)
      (fun i => a*ω i) (fun i => γ*ω i) w σ).inPhysical (metricRoot A)⁻¹
    (S 1).base=A ∧ (S (-1)).base=A ∧
      (S 1).FrobeniusAdmissible N A r ω w τ ∧ (S (-1)).FrobeniusAdmissible N A r ω w τ ∧
      sharpConstant W w/Real.sqrt 2-2*(W+w)^3≤
        max ((S 1).outputRatio m g N) ((S (-1)).outputRatio m g N) := by
  -- Choose the genuine Frobenius maximizer once for the entire original primitive profile.
  let W := ∑ i∈range N, ω i
  let a := maximizingCross W w/Real.sqrt 2
  let γ := maximizingComplement W w
  have hW : 0≤W := sum_nonneg fun i hi => hω i (mem_range.mp hi)
  obtain ⟨hγ,hcross,hcircle⟩ := maximizing_coordinates hW hw
  have hroot : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hroot2 : (Real.sqrt 2)^2=(2 : ℝ) := Real.sq_sqrt (by norm_num)
  have ha : 0≤a := div_nonneg hcross hroot.le
  have hac : 2*a^2+γ^2=1 := by
    have hsq : 2*a^2=maximizingCross W w^2 := by dsimp only [a]; rw [div_pow,hroot2]; ring
    nlinarith
  have ha₁ : a≤1 := by nlinarith [sq_nonneg γ]
  have hγ₁ : γ≤1 := by nlinarith [sq_nonneg a]
  have ho := canonicalCG_frame_of_full_atoms A hA g hcount
  let e := canonicalCGUnitStep A g 0
  let f := canonicalCGUnitStep A g N
  have he : ‖e‖=1 := by simpa only [e,Fin.val_zero] using ho.norm_eq_one (0 : Fin (N+1))
  have hf : ‖f‖=1 := by simpa only [f,Fin.val_last] using ho.norm_eq_one (Fin.last N)
  have hef : inner ℝ e f=0 := by
    simpa only [e,f,Fin.val_zero,Fin.val_last] using ho.inner_eq_zero (i := 0) (j := Fin.last N)
      (by intro h; have hv : (0 : ℕ)=N := congrArg Fin.val h; omega)
  refine ⟨physical_knownBasePlanarScenario_base A hA e f _ _ w 1,
    physical_knownBasePlanarScenario_base A hA e f _ _ w (-1),
    knownBasePlanarScenario_frobenius_admissible A hA e f he hf hef ω w τ r N hω hw hτ hr a γ 1 hac (by norm_num),
    knownBasePlanarScenario_frobenius_admissible A hA e f he hf hef ω w τ r N hω hw hτ hr a γ (-1) hac (by norm_num),?_⟩
  -- The real source execution has the true maximizing quadratic numerator on both admissible signs.
  have hsum (b : ℝ) : (∑ i∈range N, b*ω i)=b*W := (mul_sum _ _ _).symm
  have hX : 0≤∑ i∈range N, a*ω i := by rw [hsum]; positivity
  have hβ : 0≤(∑ i∈range N, γ*ω i)+w := by rw [hsum]; positivity
  have hXs : (∑ i∈range N, a*ω i)≤W+w := by
    rw [hsum]
    have hh := mul_le_mul_of_nonneg_right ha₁ hW
    linarith
  have hβs : (∑ i∈range N, γ*ω i)+w≤W+w := by
    rw [hsum]
    exact add_le_add (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hγ₁ hW) le_rfl
  have hl := knownBasePlanarScenario_lower A hA g hN hcount m hm h1
    (fun i => a*ω i) (fun i => γ*ω i) w (W+w) hX hβ hXs hβs hs
  have hvalue : (∑ i∈range N, a*ω i)*((∑ i∈range N, γ*ω i)+w)=sharpConstant W w/Real.sqrt 2 := by
    rw [hsum,hsum]
    dsimp only [a,γ,sharpConstant]
    ring
  rw [hvalue] at hl
  exact hl

end
end krylov.Information
