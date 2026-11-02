import jacobi.Reference.AbelIntegral
import jacobi.Reference.BetaNormalization

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: the Mehler--Dirichlet formula, DLMF 14.12.1, derived here from
the proved Euler transformation and genuine beta convolution.
Use: puts the Euler-transformed Mehler integral in the exact parameter order of waveCore.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Real Set MeasureTheory _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The actual Gauss function is symmetric in its two numerator parameters, with no nontermination restriction.
Use: puts the Euler-transformed Mehler integral in the exact parameter order of waveCore.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: symmetry of Gauss's rising-factorial coefficients, as proved in mathlib.
Proof: apply the sum operation and evaluation to the community equality of the original multilinear series. -/
theorem numerator_symm (a b c z : ℂ) :
    ordinaryHypergeometric a b c z=ordinaryHypergeometric b a c z := by
  exact congrArg (fun p => FormalMultilinearSeries.sum p z)
    (ordinaryHypergeometricSeries_symm (𝔸 := ℂ) a b c)

/-- The positive physical angular coordinate combines its two endpoint powers into the exact sine power.
Use: cancels all half-angle powers in mehler_reference_identity without choosing an artificial complex power branch.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: x*(1-x)=(sin(theta)/2)^2 by the circle identity. Combine real powers only at positive physical bases. -/
theorem angular_power (g : ℝ) {theta : ℝ} (htheta : theta∈Ioo (0:ℝ) Real.pi) :
    (2:ℝ)^(2*g-1)*(angularCoordinate theta)^(g-1/2)*
      (1-angularCoordinate theta)^(g-1/2)=(Real.sin theta)^(2*g-1) := by
  -- Both factors of the beta coordinate are strictly positive before the far endpoint.
  have hx := angularCoordinate_pos htheta
  have hy := (angularCoordinate_mem ⟨htheta.1.le,htheta.2⟩).2
  have hs := Real.sin_pos_of_pos_of_lt_pi htheta.1 htheta.2
  have hc : angularCoordinate theta*(1-angularCoordinate theta)=(Real.sin theta/2)^2 := by
    dsimp [angularCoordinate]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  rw [mul_assoc,← Real.mul_rpow hx.le (sub_nonneg.mpr hy.le),hc,
    ← Real.rpow_natCast_mul (by positivity : 0≤Real.sin theta/2),
    Nat.cast_ofNat,show (2:ℝ)*(g-1/2)=2*g-1 by ring,
    Real.div_rpow hs.le (by norm_num)]
  field_simp [(Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*g-1)).ne']

/-- The literal Mehler--Dirichlet integral equals the actual reference Gauss expression with the original symmetric beta normalization.
Use: identifies the defining sine integral with wave and solution, fixing every scalar before negative-energy comparisons.
Article: jacobi, Lemma C.1.
Source: Mehler--Dirichlet integral, DLMF 14.12.1, proved here including its normalization.
Proof: evaluate the genuine singular integral by beta convolution, use
Euler's transformation on its physical convergence interval, and apply
Gamma duplication and angular_power to the exact real scalar factors. -/
theorem mehler_reference_identity {g theta : ℝ} (hg : 0<g)
    (htheta : theta∈Ioo (0:ℝ) Real.pi) (lam : ℂ) :
    (∫ v in (0:ℝ)..theta,(((Real.cos v-Real.cos theta)^(g-1):ℝ):ℂ)*
        Complex.cos (lam*(v:ℂ)))=
      (((2:ℝ)^(g-1)*betaNormalization g*(Real.sin theta)^(2*g-1):ℝ):ℂ)*
        ordinaryHypergeometric ((g:ℂ)-lam) ((g:ℂ)+lam)
          ((g:ℂ)+1/2) (angularCoordinate theta:ℂ) := by
  -- The independently proved integral evaluation retains the original interval and singular endpoint powers.
  let x := angularCoordinate theta
  have hx : x∈Ioo (0:ℝ) 1 :=
    ⟨angularCoordinate_pos htheta,(angularCoordinate_mem ⟨htheta.1.le,htheta.2⟩).2⟩
  have hn : ‖(x:ℂ)‖<1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx.1]
    exact hx.2
  have he := euler_transform (a := (1/2:ℂ)-lam) (b := (1/2:ℂ)+lam)
    (c := (1/2:ℂ)+(g:ℂ)) (by norm_num; linarith) hn
  have hpow : (1-(x:ℂ))^((1/2:ℂ)+(g:ℂ)-((1/2:ℂ)-lam)-((1/2:ℂ)+lam))=
      (((1-x)^(g-1/2):ℝ):ℂ) := by
    rw [show (1/2:ℂ)+(g:ℂ)-((1/2:ℂ)-lam)-((1/2:ℂ)+lam)=((g-1/2:ℝ):ℂ) by push_cast; ring,
      show (1:ℂ)-(x:ℂ)=((1-x:ℝ):ℂ) by push_cast; rfl,
      Complex.ofReal_cpow (sub_pos.mpr hx.2).le]
  have hbeta : Complex.Gamma (1/2:ℂ)*Complex.Gamma (g:ℂ)/Complex.Gamma ((1/2:ℂ)+(g:ℂ))=
      (((2:ℝ)^(2*g-1)*betaNormalization g:ℝ):ℂ) := by
    rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by push_cast; rfl,
      show ((1/2:ℝ):ℂ)+(g:ℂ)=((g+1/2:ℝ):ℂ) by push_cast; ring,
      Complex.Gamma_ofReal,Complex.Gamma_ofReal,Complex.Gamma_ofReal]
    exact_mod_cast half_beta_normalization hg
  have hparam1 : (1/2:ℂ)+(g:ℂ)-((1/2:ℂ)-lam)=(g:ℂ)+lam := by ring
  have hparam2 : (1/2:ℂ)+(g:ℂ)-((1/2:ℂ)+lam)=(g:ℂ)-lam := by ring
  rw [hpow,hparam1,hparam2,numerator_symm ((g:ℂ)+lam) ((g:ℂ)-lam)] at he
  dsimp only [x] at he
  rw [add_comm (1/2:ℂ) (g:ℂ)] at he
  have hp := congrArg Complex.ofReal (angular_power g htheta)
  push_cast at hp
  rw [mehler_beta_identity hg htheta,hbeta,add_comm (1/2:ℂ) (g:ℂ),he]
  push_cast
  linear_combination (((2:ℝ)^(g-1):ℝ):ℂ)*(betaNormalization g:ℂ)*
    ordinaryHypergeometric ((g:ℂ)-lam) ((g:ℂ)+lam) ((g:ℂ)+1/2) (x:ℂ)*hp

end
end jacobi.Reference.Hypergeometric
