import krylov.Envelope.CorrectionProgramJets
import krylov.Envelope.JetLists

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, all actual correction observation jets.
Use: place the true complete intermediate correction-observation list in
the real enlarged first-jet flag, including every actual zero query and
every genuine returned gradient, with its true finite query count.
Source: genuine correction-program moving-span derivatives, actual zero
reference queries and exact even/odd true observation-coordinate identities.
-/

namespace krylov.Envelope
noncomputable section
open Filter Topology Matrix krylov.Methods krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m p : ℕ}

/-- A real smooth gradient differs from a genuinely coherent observation by an admissible true vertical jet when their actual reference values agree.
Use: A real smooth gradient differs from a genuinely coherent observation by an admissible true vertical jet when their actual reference values agree.
Article: main_krylov, apB:lem:filtration, all actual correction observation jets.
Proof: Differentiate the actual difference, then add its real vertical first jet to the genuine incoming observation jet. -/
theorem jetSubspace_of_difference (K : Submodule ℝ E) (L : E →ₗ[ℝ] E)
    (v g : ℝ → E) (hv : ContDiffAt ℝ 2 v 0) (hg : ContDiffAt ℝ 2 g 0)
    (hz : v 0=g 0) (hj : (g 0,deriv g 0)∈jetSubspace K L)
    (hdiff : deriv (fun t => v t-g t) 0∈K) :
    (v 0,deriv v 0)∈jetSubspace K L := by
  have he := ((hv.differentiableAt (by norm_num)).hasDerivAt.sub
    (hg.differentiableAt (by norm_num)).hasDerivAt).deriv
  change deriv (fun t => v t-g t) 0=deriv v 0-deriv g 0 at he
  rw [he] at hdiff
  have h := (jetSubspace K L).add_mem hj (jetSubspace_vertical K L hdiff)
  simpa only [Prod.mk_add_mk,add_zero,add_sub_cancel,hz] using h

/-- Every actual complete correction-program observation jet lies in the genuine prescribed flag when both the true query span and its real reference image lie there.
Use: Every actual complete correction-program observation jet lies in the genuine prescribed flag when both the true query span and its real reference image lie there.
Article: main_krylov, apB:lem:filtration, all actual correction observation jets.
Proof: Use the actual primitive program regularity and moving-span derivative theorem. The true fixed query count identifies all real finite coordinates: even coordinates are genuine zero-query jets, odd coordinates are true incoming gradients plus actual image-span derivative shifts; real out-of-range coordinates are zero. -/
theorem correction_program_observation_jets (K : Submodule ℝ E) (L : E →ₗ[ℝ] E)
    (P : CorrectionProgram E m)
    (B : ℝ → E →L[ℝ] E) (g : ℝ → E) (data : ℝ → Fin m → E) (s : ℝ → Fin p → E)
    (hB : ContDiffAt ℝ 2 B 0) (hg : ContDiffAt ℝ 2 g 0) (hd : ContDiffAt ℝ 2 data 0)
    (hs : ∀ i, ContDiffAt ℝ 2 (fun t => s t i) 0)
    (hP : P.RegularAt 2 (B 0) (g 0) (data 0))
    (hzero : ZeroCorrections (P.tree (data 0)) (B 0) (g 0))
    (hspan : ∀ᶠ t in 𝓝 (0 : ℝ), (P.tree (data t)).InSubspace (Submodule.span ℝ (Set.range (s t))))
    (hGram : (crossGram (s 0) (s 0)).det≠0)
    (hImageGram : (crossGram (fun i => B 0 (s 0 i)) (fun i => B 0 (s 0 i))).det≠0)
    (hK : Submodule.span ℝ (Set.range (s 0))≤K)
    (hBK : Submodule.span ℝ (Set.range fun i => B 0 (s 0 i))≤K)
    (hgj : (g 0,deriv g 0)∈jetSubspace K L) :
    JetListAt (jetSubspace K L) (fun t => correctionObservations
      (runCorrections (P.tree (data t)) (B t) (g t)).trace) := by
  -- Keep the true finite executor and its actual complete trace throughout the coordinate proof.
  let R := fun t => runCorrections (P.tree (data t)) (B t) (g t)
  have hreg := P.run_regular B g data 0 hB hg hd hP
  have hjets := correction_program_zero_jets P B g data s hB hg hd hs hP hzero hspan hGram hImageGram
  refine ⟨hreg.2.2,?_⟩
  intro i
  let j := i/2
  have hcount (t : ℝ) : (R t).trace.length=P.queryCount := P.trace_length _ _ _
  by_cases hj : j < P.queryCount
  · have hmem : (R 0).trace.getD j (0,0)∈(R 0).trace := by
      rw [List.getD_eq_get _ _ ⟨j,by rw [hcount];exact hj⟩]
      exact List.get_mem _ _
    -- The true nonstagnating reference phase records only zero queries and the actual incoming gradient.
    have hz := zeroCorrections_trace _ _ _ hzero _ hmem
    have hj' := hjets.2 ⟨j,hj⟩
    by_cases hi : i%2=0
    · have hi' : i=2*j := by dsimp [j];omega
      simp_rw [hi',correctionObservations,correctionObservations_getD_even]
      rw [show ((R 0).trace.getD j (0,0)).1=0 from hz.1]
      exact jetSubspace_vertical K L (hK hj'.1)
    · have hi' : i=2*j+1 := by dsimp [j];omega
      simp_rw [hi',correctionObservations,correctionObservations_getD_odd]
      have hv : ContDiffAt ℝ 2 (fun t => ((R t).trace.getD j (0,0)).2) 0 := by
        convert hreg.2.2.getD (2*j+1) using 1
        funext t
        exact (correctionObservations_getD_odd (R t).trace (0 : E) j).symm
      exact jetSubspace_of_difference K L _ g hv hg hz.2 hgj (hBK hj'.2)
    -- Genuine absent coordinates remain zero because the primitive program has this true fixed query count.
  · have he (t : ℝ) : (correctionObservations (R t).trace).getD i 0=0 := by
      apply List.getD_eq_default
      rw [correctionObservations_length,hcount]
      dsimp [j] at hj
      omega
    change ((correctionObservations (R 0).trace).getD i 0,deriv (fun t => (correctionObservations (R t).trace).getD i 0) 0)∈_
    simp only [he,deriv_const]
    exact (jetSubspace K L).zero_mem
end
end krylov.Envelope
