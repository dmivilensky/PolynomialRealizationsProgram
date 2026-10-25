import polyak.FareyPlateau.Ray.ContactDerivative
import Mathlib.Topology.Order.Compact

/-! The actual infimum defining a_F ranges over every finite admissible
signed-lag support.  No lag cutoff or numerical grid enters this definition. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set
open scoped BigOperators

structure SourceCertificate (j k : ℕ) (b : ℤ) (D : ℝ) where
  card : ℕ
  lag : Fin card→ℤ
  weight : Fin card→ℝ
  admissible : Symbols.Admissible k b
    (edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D) lag weight

def SourceCertificate.R {j k : ℕ} {b : ℤ} {D : ℝ}
    (C : SourceCertificate j k b D) : ℝ→ℝ :=
  Symbols.curvatureQuotient C.lag C.weight (Chart.rationalCosine j k)
    (Chart.rationalHeight j k) D

theorem SourceCertificate.continuous_R {j k : ℕ} {b : ℤ} {D : ℝ}
    (C : SourceCertificate j k b D) : ContinuousOn C.R (Icc (-1:ℝ) 1) :=
  Symbols.curvatureQuotient_continuousOn C.lag C.weight C.admissible.nonzero
    (fun i=>(C.admissible.positive i).le) C.admissible.normalization C.admissible.bezout
    ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩

def SourceCertificate.maximum {j k : ℕ} {b : ℤ} {D : ℝ}
    (C : SourceCertificate j k b D) : ℝ := sSup (C.R '' Icc (-1:ℝ) 1)

theorem SourceCertificate.maximum_spec {j k : ℕ} {b : ℤ} {D : ℝ}
    (C : SourceCertificate j k b D) :
    (∃c∈Icc (-1:ℝ) 1,C.R c=C.maximum) ∧
      ∀c∈Icc (-1:ℝ) 1,C.R c≤C.maximum := by
  have hn : (C.R '' Icc (-1:ℝ) 1).Nonempty :=
    (by norm_num : (Icc (-1:ℝ) 1).Nonempty).image C.R
  have hc := isCompact_Icc.image_of_continuousOn C.continuous_R
  have hg := hc.isGreatest_sSup hn
  obtain ⟨c,hc,he⟩ := hg.1
  refine ⟨⟨c,hc,he⟩,?_⟩
  intro x hx
  exact hg.2 ⟨x,hx,rfl⟩

theorem SourceCertificate.maximum_lt_iff {j k : ℕ} {b : ℤ} {D a : ℝ}
    (C : SourceCertificate j k b D) : C.maximum<a ↔ ∀c∈Icc (-1:ℝ) 1,C.R c<a := by
  constructor
  · intro ha c hc
    exact (C.maximum_spec.2 c hc).trans_lt ha
  · intro h
    obtain ⟨c,hc,he⟩ := C.maximum_spec.1
    rw [←he]
    exact h c hc

def aF (j k : ℕ) (b : ℤ) (D : ℝ) : ℝ :=
  sInf (Set.range (SourceCertificate.maximum (j:=j) (k:=k) (b:=b) (D:=D)))

theorem SourceCertificate.contact_value {j k : ℕ} {b : ℤ} {D : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1) :
    C.R (Chart.rationalCosine j k)=
      -(1/2:ℝ)*deriv (deriv (Symbols.psi C.lag C.weight)) (Chart.rationalCosine j k) := by
  obtain ⟨hv,hd⟩ := phaseFloor_edge_contact hj hjk hb C.admissible
  exact Symbols.curvatureQuotient_contact_value C.lag C.weight
    (C.admissible.phaseFloor_analytic _ ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩) hv hd

theorem SourceCertificate.off_contact {j k : ℕ} {b : ℤ} {D c : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1)
    (hc : c≠Chart.rationalCosine j k) :
    C.R c=(Chart.rationalHeight j k+(1+D)*(c-Chart.rationalCosine j k)-
      Symbols.psi C.lag C.weight c)/(c-Chart.rationalCosine j k)^2 := by
  obtain ⟨hv,hd⟩ := phaseFloor_edge_contact hj hjk hb C.admissible
  exact Symbols.curvatureQuotient_off_contact C.lag C.weight
    (C.admissible.phaseFloor_analytic _ ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩) hv hd hc

end polyak.FareyPlateau.Ray
