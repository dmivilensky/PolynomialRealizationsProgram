import polyak.FiniteHorizon.BandedEstimate

/-!
Article: Appendix C, the zero-kernel closure argument for a uniform prefactor.
Use: a concrete separated finite kernel yields energy localization, strict
kernel contraction, compact near-kernel contraction, and the genuine envelope
bound. Every passage retains all finite dimensions and all horizons.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy
open scoped BigOperators

theorem exists_prefactor_of_kernel_banded {A B β T ε : ℝ} {H : ℕ}
    (hB : B≠0) (L : WindowPrice H) (hRate : growthRate A B β H≤Real.exp T)
    (hpos : PriceNonnegative A B β H L) (hstep : PriceContracts A B β H T L)
    (K : Kernel) (S : Finset ℕ) (d : ℕ → ℝ)
    (hε : 0<ε) (hneg : ∀ θ,kernelSymbol K θ≤ -ε) (hcharge : ∑ n∈S,d n=0)
    (N : ℕ)
    (hsource : ∀ D : ℕ,∀ r : HRun (EuclideanSpace ℝ (Fin D)) A B β H,
      ZeroPriceRun L r → ∀ k,N≤k →
        0≤kernelEval K (discountedInteger r.x T) k+
          finiteValueCombination S d (discountedValue (sampleValue r) T) k) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,envelope A B β H n≤C*Real.exp ((n : ℝ)*T) := by
  obtain ⟨M,w,hM,henergy⟩:=kernelWindowEnergyBound_of_banded L K S d hε hneg hcharge N hsource
  obtain ⟨p,hp,hkernel⟩:=exists_kernel_trace_contraction hB L hRate hpos hstep hM henergy
  obtain ⟨η,hη,hnear⟩:=exists_nearKernelBound_of_normalized hB L hpos hkernel
  exact exists_envelope_prefactor hB L hstep hp hη hnear

end polyak.FiniteHorizon
