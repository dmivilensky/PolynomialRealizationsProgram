import jacobi.Bessel.OrderShift
import jacobi.Reference.CosineHypergeometric

/-!
Article: jacobi, Proposition C.4.
The actual normalized Bessel functions at orders -1/2 and 1/2 are
the original cosine and sine functions, with their exact endpoint
normalization. The proofs concern genuine entire functions and their
actual derivatives, including the removable frequency origin.
Source: the half-integer Bessel identities, DLMF 10.16.1.
Use: proves normalized_neg_half from the genuine original Bessel equation and analytic initial-value uniqueness.
-/
namespace jacobi.Bessel
noncomputable section
open Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

/-- The original normalized Bessel function of order -1/2 composed with the squared frequency solves the actual harmonic equation.
Use: proves normalized_neg_half from the genuine original Bessel equation and analytic initial-value uniqueness.
Article: jacobi, Proposition C.4.
Source: the half-integer Bessel identity, DLMF 10.16.1.
Proof: differentiate the true squared-frequency composition twice.
Its second derivative is 2*N'+4*w^2*N''; the proved Bessel equation
at order -1/2 makes this exactly -N, including at w=0. -/
theorem neg_half_frequency_equation (w : ℂ) :
    deriv (deriv (fun z : ℂ => normalized (-1/2) (z^2))) w=
      -normalized (-1/2) (w^2) := by
  -- Every derivative belongs to the actual original entire Bessel function.
  let N : ℂ → ℂ := normalized (-1/2)
  let F : ℂ → ℂ := fun z => N (z^2)
  let S : ℂ → ℂ := fun z => 2*z*deriv N (z^2)
  have hF (z : ℂ) : HasDerivAt F (S z) z := by
    convert! ((normalized_analytic (-1/2) (z^2)).differentiableAt.hasDerivAt).comp z
      ((hasDerivAt_id z).pow 2) using 1
    dsimp [S,N]
    norm_num
    ring
  have he : deriv F=S := funext (fun z => (hF z).deriv)
  have hS := (((hasDerivAt_id w).const_mul 2).mul
    (((normalized_analytic (-1/2) (w^2)).deriv.differentiableAt.hasDerivAt).comp w
      ((hasDerivAt_id w).pow 2)))
  change HasDerivAt S _ w at hS
  change deriv (deriv F) w= -N (w^2)
  rw [he,hS.deriv]
  have hh := normalized_equation (a := (-1/2:ℂ)) (by norm_num) (w^2)
  dsimp only [N,id_eq,Pi.pow_apply] at *
  norm_num at *
  linear_combination hh

/-- The actual original normalized Bessel function of order -1/2 is exactly cosine at every complex squared frequency.
Use: identifies the complete special-order Bessel spectrum and the original Bessel Poisson integral before the characteristic normalization comparison.
Article: jacobi, Proposition C.4.
Source: DLMF 10.16.1, proved here from the actual Bessel equation.
Proof: both entire frequency functions solve the genuine harmonic
equation, have value one and derivative zero at zero. Analytic
initial-value uniqueness gives a zero difference near zero; the
identity theorem extends it throughout the entire complex plane. -/
theorem normalized_neg_half (w : ℂ) : normalized (-1/2) (w^2)=Complex.cos w := by
  -- The initial data are those of the same actual normalized entire function used in the Bessel spectrum.
  let F : ℂ → ℂ := fun z => normalized (-1/2) (z^2)
  have hF (z : ℂ) : AnalyticAt ℂ F z :=
    (normalized_analytic (-1/2) (z^2)).comp (f := fun u : ℂ => u^2)
      (analyticAt_id.pow 2)
  have hD : AnalyticOnNhd ℂ (F-Complex.cos) univ := fun z _ =>
    (hF z).sub (Complex.differentiable_cos.analyticAt _)
  have h0 : (F-Complex.cos) 0=0 := by simp [F,normalized_zero (a := (-1/2:ℂ)) (by norm_num)]
  have hF0 : deriv F 0=0 := by
    have hh : HasDerivAt F 0 0 := by
      convert! HasDerivAt.comp (h₂ := normalized (-1/2)) (h := fun z : ℂ => z^2) (0:ℂ)
        (normalized_analytic (-1/2) ((0:ℂ)^2)).differentiableAt.hasDerivAt
          ((hasDerivAt_id (0:ℂ)).pow 2) using 1
      simp
    exact hh.deriv
  have h1 : deriv (F-Complex.cos) 0=0 := by
    rw [deriv_sub (hF 0).differentiableAt Complex.differentiable_cos.differentiableAt,hF0]
    simp
  have hfirst : deriv (F-Complex.cos)=deriv F-deriv Complex.cos := by
    funext z
    exact deriv_sub (hF z).differentiableAt Complex.differentiable_cos.differentiableAt
  have hsecond : deriv (deriv (F-Complex.cos))=fun z => -(F-Complex.cos) z := by
    funext z
    rw [hfirst,deriv_sub (hF z).deriv.differentiableAt
      (Complex.differentiable_cos.analyticAt z).deriv.differentiableAt,
      neg_half_frequency_equation,Complex.deriv_cos',deriv.fun_neg,
      Complex.deriv_sin]
    simp only [Pi.sub_apply,F]
    ring
  have hnear := jacobi.Reference.Hypergeometric.constant_ode_zero (A := (-1:ℂ))
    (hD 0 (mem_univ _)) h0 h1 (by
      filter_upwards with z
      rw [hsecond]
      simp)
  exact sub_eq_zero.mp (hD.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ (0:ℂ)) hnear (mem_univ w))

/-- The actual normalized Bessel function of order 1/2 is the original entire sine quotient, stated without division at the removable origin.
Use: identifies the special-order sine spectrum and exact original normalization in Proposition C.2 at alpha=1/2.
Article: jacobi, Proposition C.4.
Source: DLMF 10.16.1 and the adjacent-order differentiation identity, both proved here.
Proof: differentiate the proved exact cosine identity and substitute
the genuine adjacent-order Bessel derivative. Its factor 2*w cancels
the order-shift scalar -1/2; the equality also holds at w=0. -/
theorem normalized_half (w : ℂ) : w*normalized (1/2) (w^2)=Complex.sin w := by
  -- Both derivatives are those of the already identified actual entire frequency functions.
  have h : HasDerivAt (fun z : ℂ => normalized (-1/2) (z^2))
      (deriv (normalized (-1/2)) (w^2)*(2*w)) w := by
    convert! HasDerivAt.comp (h₂ := normalized (-1/2)) (h := fun z : ℂ => z^2) w
      (normalized_analytic (-1/2) (w^2)).differentiableAt.hasDerivAt
        ((hasDerivAt_id w).pow 2) using 1
    simp
  have he : (fun z : ℂ => normalized (-1/2) (z^2))=Complex.cos := funext normalized_neg_half
  change HasDerivAt (fun z : ℂ => normalized (-1/2) (z^2)) _ w at h
  rw [he] at h
  have hd := h.unique (Complex.hasDerivAt_cos w)
  rw [normalized_derivative_order_shift (a := (-1/2:ℂ)) (by norm_num),
    show (-1/2:ℂ)+1=1/2 by ring] at hd
  norm_num only [Nat.cast_ofNat,pow_one] at hd
  linear_combination -hd

end
end jacobi.Bessel
