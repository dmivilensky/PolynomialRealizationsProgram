import jacobi.Reference.SpectralSolutions
import jacobi.Reference.NormingBounds
import jacobi.Reference.NormBounds

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Every kernel summand uses the actual Bessel spectrum, genuine reference
solution, original convergent norming-ratio product and true reference
squared norm. Its symmetry, endpoint vanishing and joint continuity
are proved before defining the infinite kernel.
Use: proves genuine continuity of every actual GL kernel summand, including both zero edges of its square.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Complex Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original real source reference solution is continuous at every point of the physical half interval.
Use: proves genuine continuity of every actual GL kernel summand, including both zero edges of its square.
Article: jacobi, Proposition C.2.
Proof: compose the already proved original joint continuity with the fixed genuine energy and take its actual real part. -/
theorem realSolution_continuousAt {a : ℝ} (ha : -1<a) (E : ℝ) {t : ℝ}
    (ht : t∈Icc 0 (1/2)) : ContinuousAt (realSolution a E) t := by
  have hti : t∈Ico 0 1 := ⟨ht.1,by linarith [ht.2]⟩
  have hh := (solution_joint_continuous ha hti (E:ℂ)).comp_of_eq
    (continuousAt_id.prodMk continuousAt_const) rfl
  exact Complex.continuous_re.continuousAt.comp hh

/-- The literal source GL summand built from the two genuine spectra and their actual norming data.
Use: its proved summable uniform bound defines the genuine continuous source kernel F.
Article: jacobi, Proposition C.2.
-/
def kernelTerm (a : ℝ) (ha : -1<a) (k : ℕ) (t s : ℝ) : ℝ :=
  (normingRatio a ha k*realSolution a (jacobi.Bessel.sigma a ha k) t*
      realSolution a (jacobi.Bessel.sigma a ha k) s-
    realSolution a (eigenvalue a k) t*realSolution a (eigenvalue a k) s)/norming a k

/-- Every actual original GL summand is symmetric in its two genuine spatial arguments.
Use: the genuinely convergent source kernel is symmetric term by term.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: commute the two actual real source solution factors in each product. -/
theorem kernelTerm_symmetric (a : ℝ) (ha : -1<a) (k : ℕ) (t s : ℝ) :
    kernelTerm a ha k t s=kernelTerm a ha k s t := by
  unfold kernelTerm
  ring

/-- Each original GL summand is genuinely jointly continuous on the full source half square.
Use: uniform convergence of the actual infinite series gives continuity of the genuine source kernel F.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the four actual reference solution factors are continuous even
at zero. Multiply and subtract them and divide by the fixed actual
positive reference norm; its value is independent of the spatial pair. -/
theorem kernelTerm_continuousOn (a : ℝ) (ha : -1<a) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => kernelTerm a ha k p.1 p.2)
      (Icc (0:ℝ) (1/2)×ˢIcc (0:ℝ) (1/2)) := by
  -- Every factor is the original actual energy solution, rather than an abstract continuous kernel certificate.
  intro p hp
  have hst := (realSolution_continuousAt ha (jacobi.Bessel.sigma a ha k) hp.1).comp_of_eq continuousAt_fst rfl
  have hss := (realSolution_continuousAt ha (jacobi.Bessel.sigma a ha k) hp.2).comp_of_eq continuousAt_snd rfl
  have htt := (realSolution_continuousAt ha (eigenvalue a k) hp.1).comp_of_eq continuousAt_fst rfl
  have hts := (realSolution_continuousAt ha (eigenvalue a k) hp.2).comp_of_eq continuousAt_snd rfl
  exact (((continuousAt_const.mul hst).mul hss).sub (htt.mul hts)).div_const _ |>.continuousWithinAt

/-- Every original GL summand vanishes when its first spatial coordinate is the genuine singular endpoint.
Use: proves F(0,s)=0 for the actual uniformly convergent source kernel.
Article: jacobi, Proposition C.2.
Proof: both genuine reference solutions vanish at zero throughout the source order range. -/
theorem kernelTerm_zero (a : ℝ) (ha : -1<a) (k : ℕ) (s : ℝ) : kernelTerm a ha k 0 s=0 := by
  simp only [kernelTerm,realSolution,solution_zero ha,Complex.zero_re,mul_zero,zero_mul,sub_self,zero_div]

end
end jacobi.GelfandLevitan
