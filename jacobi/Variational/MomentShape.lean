import jacobi.Young.RadialPotential
import jacobi.Variational.RadialTopGradient
import jacobi.Variational.RadialSupport
import jacobi.Variational.TopKKT

/-!
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Both actual moment minimizers have positive normal multipliers and their
printed active spectral constraints. Their actual KKT coefficient is
continuous, even and strictly decreasing at nonnegative radii. The original
measurable density is positive either on the whole line or on one finite
centered interval, up to a null set. All gradient and support premises are
proved for the actual optimizing density and selected top vector.
Source: the full normal multiplier theorem and proved strict radial gradients.
Use: transfers the actual gradient properties to the printed KKT coefficient c=mu*gamma-lambda.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set jacobi.Young
open chebyshev2.Sobolev chebyshev2.Continuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Positive multiplier scaling preserves the complete continuous strict radial gradient shape.
Use: transfers the actual gradient properties to the printed KKT coefficient c=mu*gamma-lambda.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: continuity and evenness commute with affine scalars, and a positive scalar preserves strict decrease. -/
theorem kkt_coefficient_shape {γ : ℝ → ℝ} (hc : Continuous γ) (he : ∀ x,γ (-x)=γ x)
    (ha : StrictAntiOn γ (Ici 0)) {μ : ℝ} (hμ : 0<μ) (l : ℝ) :
    Continuous (fun x => μ*γ x-l) ∧ (∀ x,μ*γ (-x)-l=μ*γ x-l) ∧
      StrictAntiOn (fun x => μ*γ x-l) (Ici 0) := by
  refine ⟨(hc.const_mul μ).sub continuous_const,fun x => by rw [he],?_⟩
  intro x hx y hy hxy
  exact sub_lt_sub_right (mul_lt_mul_of_pos_left (ha hx hy hxy) hμ) l

/-- Every actual second-moment minimizer has the full strict KKT coefficient and centered interval support.
Use: completes all shape clauses of the article's single-moment optimality theorem for i=2.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: use the actual second-moment KKT multipliers. Its literal gradient
2W_2 is positive, continuous, even, strictly decreasing and tends to zero.
The common radial support theorem then gives the complete support alternatives. -/
theorem second_minimizer_shape {M T : ℝ} (hT : 0<T) (m : Density) (hm : 0<m.mass)
    (hs : SymmetricDecreasing m.value) (hmM : m.mass≤M) (hmT : T≤observe m .second)
    (hmin : m.cost=relaxedInfimum {Observation.second} M (fun _ => T)) :
    observe m .second=T ∧ ∃ μ l : ℝ,0<μ ∧ 0≤l ∧ l*(M-m.mass)=0 ∧
      (fun x => sqrt (m.value x))=ᵐ[volume] (fun x => (2/3:ℝ)*max (2*μ*potential m x-l) 0) ∧
      Continuous (fun x => 2*μ*potential m x-l) ∧
      (∀ x,2*μ*potential m (-x)-l=2*μ*potential m x-l) ∧
      StrictAntiOn (fun x => 2*μ*potential m x-l) (Ici 0) ∧
      ((l=0 ∧ ∀ᵐ x : ℝ,0<m.value x) ∨
        (0<l ∧ ∃ a : ℝ,0<a ∧ ∀ᵐ x : ℝ,(0<m.value x ↔ |x|<a))) := by
  -- The original KKT formula is rewritten with its actual bounded Green gradient.
  obtain ⟨hG,μ,l,hμ,hl,hcomp,he⟩ := second_minimizer_kkt hT m hm hs hmM hmT hmin
  let γ (x : ℝ) := 2*potential m x
  have hγc : Continuous γ := (potential_continuous m).1.const_mul 2
  have hγe (x : ℝ) : γ (-x)=γ x := by dsimp only [γ]; rw [potential_even m hs]
  have hγp (x : ℝ) : 0<γ x := mul_pos (by norm_num) (potential_pos m hm x)
  have hγanti : StrictAntiOn γ (Ici 0) := fun x hx y hy hxy =>
    mul_lt_mul_of_pos_left (potential_strictAnti m hm hs hx hy hxy) (by norm_num)
  have hγlim : Tendsto γ atTop (𝓝 0) := by
    simpa only [mul_zero] using ((potential_sobolev m).tendsto_zero.1.const_mul 2)
  have he' : (fun x => sqrt (m.value x))=ᵐ[volume] fun x => (2/3:ℝ)*max (μ*γ x-l) 0 := by
    convert he using 1
    funext x
    dsimp only [γ]
    congr 2
    ring
  have hshape := kkt_coefficient_shape hγc hγe hγanti hμ l
  have hsupp := kkt_radial_support m hm γ hγc hγp hγe hγanti hγlim hμ hl he'
  have hecoeff : (fun x => 2*μ*potential m x-l)=(fun x => μ*γ x-l) := by funext x; dsimp only [γ]; ring
  rw [← hecoeff] at hshape
  exact ⟨hG,μ,l,hμ,hl,hcomp,he,hshape.1,by intro x; rw [potential_even m hs],hshape.2.2,hsupp⟩

/-- Every actual top-constrained minimizer has the full strict KKT coefficient and centered interval support.
Use: completes all shape clauses of the single-moment optimality theorem for the actual selected top eigenvector.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: the actual top KKT theorem constructs its unit eigenvector and
normal multipliers. Ground simplicity proves the full strict shape of
that vector's actual squared gradient. Apply the common support theorem. -/
theorem top_minimizer_shape {M T : ℝ} (hT : 0<T) (m : Density) (hm : 0<m.mass)
    (hs : SymmetricDecreasing m.value) (hmM : m.mass≤M) (hmT : T≤observe m .top)
    (hmin : m.cost=relaxedInfimum {Observation.top} M (fun _ => T)) :
    observe m .top=T ∧ ∃ e : H1,‖e‖=1 ∧ densityOperator m.value e=m.spectrum 0 • e ∧
      ∃ μ l : ℝ,0<μ ∧ 0≤l ∧ l*(M-m.mass)=0 ∧
        (fun x => sqrt (m.value x))=ᵐ[volume] (fun x => (2/3:ℝ)*max (μ*topGradient e x-l) 0) ∧
        Continuous (fun x => μ*topGradient e x-l) ∧
        (∀ x,μ*topGradient e (-x)-l=μ*topGradient e x-l) ∧
        StrictAntiOn (fun x => μ*topGradient e x-l) (Ici 0) ∧
        ((l=0 ∧ ∀ᵐ x : ℝ,0<m.value x) ∨
          (0<l ∧ ∃ a : ℝ,0<a ∧ ∀ᵐ x : ℝ,(0<m.value x ↔ |x|<a))) := by
  -- Every shape conclusion uses the actual unit vector returned by the KKT theorem.
  obtain ⟨hG,e,he,hTe,μ,l,hμ,hl,hcomp,heq⟩ := top_minimizer_kkt hT m hm hs hmM hmT hmin
  obtain ⟨hγp,hγe,hγanti⟩ := topGradient_radial m hm hs he hTe
  obtain ⟨hc,heven,hanti⟩ := kkt_coefficient_shape (topGradient_regular e).1 hγe hγanti hμ l
  exact ⟨hG,e,he,hTe,μ,l,hμ,hl,hcomp,heq,hc,heven,hanti,
    kkt_radial_support m hm (topGradient e) (topGradient_regular e).1 hγp hγe hγanti
      (topGradient_limits e).1 hμ hl heq⟩

end
end jacobi.Variational
