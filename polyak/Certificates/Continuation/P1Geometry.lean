import polyak.Certificates.Continuation.P1Geometry.Batch000
import polyak.Certificates.Continuation.P1Geometry.Batch001
import polyak.Certificates.Continuation.P1Geometry.Batch002
import polyak.Certificates.Continuation.P1Geometry.Batch003
import polyak.Certificates.Continuation.P1Geometry.Batch004
import polyak.Certificates.Continuation.P1Geometry.Batch005
import polyak.Certificates.Continuation.P1Geometry.Batch006
import polyak.Certificates.Continuation.P1Geometry.Batch007
import polyak.Certificates.Continuation.P1Geometry.Batch008
import polyak.Certificates.Continuation.P1Geometry.Batch009
import polyak.Certificates.Continuation.P1Geometry.Batch010
import polyak.Certificates.Continuation.P1Geometry.Batch011
import polyak.Certificates.Continuation.P1Geometry.Batch012
import polyak.Certificates.Continuation.P1Geometry.Batch013
import polyak.Certificates.Continuation.P1Geometry.Batch014
import polyak.Certificates.Continuation.P1Geometry.Batch015
import polyak.Certificates.Continuation.P1Cover

/-! Article: complete scalar reserves and the endpoint neighborhood on the P1 source cover. -/
namespace polyak.Certificates.Continuation.P1.Geometry
open LeanCert.Core Numerics.Parametric Boundary.P1

theorem coreAccepted : allCoreCheck P1.slabs {precision:=-80}=true :=
  (allCoreCheck_append Batch000.coreAccepted (allCoreCheck_append Batch001.coreAccepted (allCoreCheck_append Batch002.coreAccepted (allCoreCheck_append Batch003.coreAccepted (allCoreCheck_append Batch004.coreAccepted (allCoreCheck_append Batch005.coreAccepted (allCoreCheck_append Batch006.coreAccepted (allCoreCheck_append Batch007.coreAccepted (allCoreCheck_append Batch008.coreAccepted (allCoreCheck_append Batch009.coreAccepted (allCoreCheck_append Batch010.coreAccepted (allCoreCheck_append Batch011.coreAccepted (allCoreCheck_append Batch012.coreAccepted (allCoreCheck_append Batch013.coreAccepted (allCoreCheck_append Batch014.coreAccepted Batch015.coreAccepted)))))))))))))))

def atomSlabs : List (Slab 2) := (Batch000.atomSlabs++(Batch001.atomSlabs++(Batch002.atomSlabs++(Batch003.atomSlabs++(Batch004.atomSlabs++(Batch005.atomSlabs++(Batch006.atomSlabs++(Batch007.atomSlabs++(Batch008.atomSlabs++(Batch009.atomSlabs++(Batch010.atomSlabs++(Batch011.atomSlabs++(Batch012.atomSlabs++(Batch013.atomSlabs++(Batch014.atomSlabs++Batch015.atomSlabs)))))))))))))))

theorem atomAccepted : allAtomCheck atomSlabs {precision:=-80}=true :=
  (allAtomCheck_append Batch000.atomAccepted (allAtomCheck_append Batch001.atomAccepted (allAtomCheck_append Batch002.atomAccepted (allAtomCheck_append Batch003.atomAccepted (allAtomCheck_append Batch004.atomAccepted (allAtomCheck_append Batch005.atomAccepted (allAtomCheck_append Batch006.atomAccepted (allAtomCheck_append Batch007.atomAccepted (allAtomCheck_append Batch008.atomAccepted (allAtomCheck_append Batch009.atomAccepted (allAtomCheck_append Batch010.atomAccepted (allAtomCheck_append Batch011.atomAccepted (allAtomCheck_append Batch012.atomAccepted (allAtomCheck_append Batch013.atomAccepted (allAtomCheck_append Batch014.atomAccepted Batch015.atomAccepted)))))))))))))))

theorem atomSlabs_subset {slab : Slab 2} (hm : slab∈atomSlabs) : slab∈P1.slabs := by
  simp only [atomSlabs,List.mem_append] at hm
  simp only [P1.slabs,List.mem_append]
  rcases hm with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h2))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h10))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h11)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h13)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h14))))))))))))))
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; 
    simp only [Batch015.atomSlabs,List.mem_cons,List.not_mem_nil,or_false] at h15
    subst slab
    exact List.mem_cons_self

def prefixEnd : ℝ := (7311675000000001/10000000000000000 : ℚ)

theorem atomCovered : coverCheck 0 (7311675000000001/10000000000000000) atomSlabs=true := by kernel_decide

def tailSlabs : List (Slab 2) := P1.Batch015.slabs

theorem slopeAccepted : allSlopeCheck P1.system tailSlabs {precision:=-80}=true := Batch015.slopeAccepted

theorem tailCovered : coverCheck (7306177500000001/10000000000000000) (733/1000) tailSlabs=true := by kernel_decide

theorem tailSlabs_subset {slab : Slab 2} (hm : slab∈tailSlabs) : slab∈P1.slabs := by
  simp only [P1.slabs,List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hm)))))))))))))))

end polyak.Certificates.Continuation.P1.Geometry
