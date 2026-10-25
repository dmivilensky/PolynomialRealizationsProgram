import chebyshev2.Certificates.Compact.ReferenceTrajectoryData

/-!
Article: chebyshev2, Section 4.1.
Reference Trajectory Index.
Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.rightBlock157_subset` feeds
`chebyshev2.Certificates.Compact.ContactValues.valid3` (valid3).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Certificates.Compact.ReferenceTrajectory
open chebyshev2.Numerics.IntegerCertificate
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 0
noncomputable def leftBlocks : List (List ResidualCell.Row) := [ReferenceResiduals.block0,ReferenceResiduals.block1,ReferenceResiduals.block2,ReferenceResiduals.block3,ReferenceResiduals.block4,ReferenceResiduals.block5,ReferenceResiduals.block6,ReferenceResiduals.block7,ReferenceResiduals.block8,ReferenceResiduals.block9,ReferenceResiduals.block10,ReferenceResiduals.block11,ReferenceResiduals.block12,ReferenceResiduals.block13,ReferenceResiduals.block14,ReferenceResiduals.block15,ReferenceResiduals.block16,ReferenceResiduals.block17,ReferenceResiduals.block18,ReferenceResiduals.block19,ReferenceResiduals.block20,ReferenceResiduals.block21,ReferenceResiduals.block22,ReferenceResiduals.block23,ReferenceResiduals.block24,ReferenceResiduals.block25,ReferenceResiduals.block26,ReferenceResiduals.block27,ReferenceResiduals.block28,ReferenceResiduals.block29,ReferenceResiduals.block30,ReferenceResiduals.block31,ReferenceResiduals.block32,ReferenceResiduals.block33,ReferenceResiduals.block34,ReferenceResiduals.block35,ReferenceResiduals.block36,ReferenceResiduals.block37,ReferenceResiduals.block38,ReferenceResiduals.block39,ReferenceResiduals.block40,ReferenceResiduals.block41,ReferenceResiduals.block42,ReferenceResiduals.block43,ReferenceResiduals.block44,ReferenceResiduals.block45,ReferenceResiduals.block46,ReferenceResiduals.block47,ReferenceResiduals.block48,ReferenceResiduals.block49,ReferenceResiduals.block50,ReferenceResiduals.block51,ReferenceResiduals.block52,ReferenceResiduals.block53,ReferenceResiduals.block54,ReferenceResiduals.block55,ReferenceResiduals.block56,ReferenceResiduals.block57,ReferenceResiduals.block58,ReferenceResiduals.block59,ReferenceResiduals.block60,ReferenceResiduals.block61,ReferenceResiduals.block62,ReferenceResiduals.block63,ReferenceResiduals.block64,ReferenceResiduals.block65,ReferenceResiduals.block66,ReferenceResiduals.block67,ReferenceResiduals.block68,ReferenceResiduals.block69,ReferenceResiduals.block70,ReferenceResiduals.block71,ReferenceResiduals.block72,ReferenceResiduals.block73,ReferenceResiduals.block74,ReferenceResiduals.block75,(ReferenceResiduals.block76.take 12)]
theorem leftRows_blocks : leftRows=leftBlocks.flatten := rfl
theorem leftBlock0_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block0) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block0,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inl True.intro
theorem leftBlock1_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block1) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block1,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inl True.intro)
theorem leftBlock2_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block2) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block2,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inl True.intro))
theorem leftBlock3_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block3) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block3,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inl True.intro)))
theorem leftBlock4_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block4) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block4,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))
theorem leftBlock5_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block5) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block5,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))
theorem leftBlock6_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block6) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block6,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))
theorem leftBlock7_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block7) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block7,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))
theorem leftBlock8_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block8) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block8,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))
theorem leftBlock9_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block9) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block9,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))
theorem leftBlock10_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block10) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block10,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))
theorem leftBlock11_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block11) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block11,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))
theorem leftBlock12_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block12) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block12,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))
theorem leftBlock13_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block13) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block13,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))
theorem leftBlock14_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block14) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block14,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))
theorem leftBlock15_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block15) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block15,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))
theorem leftBlock16_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block16) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block16,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))
theorem leftBlock17_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block17) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block17,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))
theorem leftBlock18_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block18) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block18,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))
theorem leftBlock19_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block19) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block19,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))
theorem leftBlock20_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block20) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block20,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))
theorem leftBlock21_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block21) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block21,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))
theorem leftBlock22_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block22) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block22,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))
theorem leftBlock23_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block23) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block23,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))
theorem leftBlock24_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block24) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block24,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))
theorem leftBlock25_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block25) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block25,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))
theorem leftBlock26_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block26) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block26,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))
theorem leftBlock27_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block27) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block27,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))
theorem leftBlock28_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block28) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block28,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))
theorem leftBlock29_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block29) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block29,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))
theorem leftBlock30_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block30) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block30,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))
theorem leftBlock31_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block31) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block31,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))
theorem leftBlock32_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block32) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block32,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))
theorem leftBlock33_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block33) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block33,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))
theorem leftBlock34_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block34) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block34,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))
theorem leftBlock35_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block35) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block35,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))
theorem leftBlock36_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block36) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block36,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))
theorem leftBlock37_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block37) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block37,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))
theorem leftBlock38_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block38) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block38,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))
theorem leftBlock39_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block39) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block39,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))
theorem leftBlock40_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block40) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block40,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))
theorem leftBlock41_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block41) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block41,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))
theorem leftBlock42_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block42) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block42,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock43_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block43) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block43,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock44_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block44) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block44,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock45_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block45) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block45,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock46_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block46) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block46,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock47_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block47) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block47,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock48_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block48) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block48,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock49_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block49) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block49,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock50_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block50) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block50,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock51_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block51) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block51,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock52_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block52) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block52,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock53_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block53) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block53,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock54_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block54) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block54,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock55_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block55) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block55,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock56_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block56) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block56,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock57_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block57) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block57,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock58_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block58) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block58,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock59_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block59) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block59,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock60_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block60) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block60,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock61_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block61) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block61,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock62_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block62) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block62,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock63_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block63) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block63,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock64_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block64) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block64,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock65_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block65) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block65,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock66_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block66) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block66,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock67_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block67) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block67,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock68_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block68) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block68,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock69_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block69) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block69,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock70_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block70) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block70,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock71_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block71) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block71,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock72_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block72) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block72,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock73_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block73) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block73,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock74_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block74) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block74,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock75_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block75) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block75,?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem leftBlock76_subset {r : ResidualCell.Row} (hr : r∈(ReferenceResiduals.block76.take 12)) : r∈leftRows := by
  rw [leftRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨(ReferenceResiduals.block76.take 12),?_,hr⟩
  simp only [leftBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
noncomputable def rightBlocks : List (List ResidualCell.Row) := [(ReferenceResiduals.block76.drop 12),ReferenceResiduals.block77,ReferenceResiduals.block78,ReferenceResiduals.block79,ReferenceResiduals.block80,ReferenceResiduals.block81,ReferenceResiduals.block82,ReferenceResiduals.block83,ReferenceResiduals.block84,ReferenceResiduals.block85,ReferenceResiduals.block86,ReferenceResiduals.block87,ReferenceResiduals.block88,ReferenceResiduals.block89,ReferenceResiduals.block90,ReferenceResiduals.block91,ReferenceResiduals.block92,ReferenceResiduals.block93,ReferenceResiduals.block94,ReferenceResiduals.block95,ReferenceResiduals.block96,ReferenceResiduals.block97,ReferenceResiduals.block98,ReferenceResiduals.block99,ReferenceResiduals.block100,ReferenceResiduals.block101,ReferenceResiduals.block102,ReferenceResiduals.block103,ReferenceResiduals.block104,ReferenceResiduals.block105,ReferenceResiduals.block106,ReferenceResiduals.block107,ReferenceResiduals.block108,ReferenceResiduals.block109,ReferenceResiduals.block110,ReferenceResiduals.block111,ReferenceResiduals.block112,ReferenceResiduals.block113,ReferenceResiduals.block114,ReferenceResiduals.block115,ReferenceResiduals.block116,ReferenceResiduals.block117,ReferenceResiduals.block118,ReferenceResiduals.block119,ReferenceResiduals.block120,ReferenceResiduals.block121,ReferenceResiduals.block122,ReferenceResiduals.block123,ReferenceResiduals.block124,ReferenceResiduals.block125,ReferenceResiduals.block126,ReferenceResiduals.block127,ReferenceResiduals.block128,ReferenceResiduals.block129,ReferenceResiduals.block130,ReferenceResiduals.block131,ReferenceResiduals.block132,ReferenceResiduals.block133,ReferenceResiduals.block134,ReferenceResiduals.block135,ReferenceResiduals.block136,ReferenceResiduals.block137,ReferenceResiduals.block138,ReferenceResiduals.block139,ReferenceResiduals.block140,ReferenceResiduals.block141,ReferenceResiduals.block142,ReferenceResiduals.block143,ReferenceResiduals.block144,ReferenceResiduals.block145,ReferenceResiduals.block146,ReferenceResiduals.block147,ReferenceResiduals.block148,ReferenceResiduals.block149,ReferenceResiduals.block150,ReferenceResiduals.block151,ReferenceResiduals.block152,ReferenceResiduals.block153,ReferenceResiduals.block154,ReferenceResiduals.block155,ReferenceResiduals.block156,ReferenceResiduals.block157]
theorem rightRows_blocks : rightRows=rightBlocks.flatten := rfl
theorem rightBlock76_subset {r : ResidualCell.Row} (hr : r∈(ReferenceResiduals.block76.drop 12)) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨(ReferenceResiduals.block76.drop 12),?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inl True.intro
theorem rightBlock77_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block77) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block77,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inl True.intro)
theorem rightBlock78_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block78) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block78,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inl True.intro))
theorem rightBlock79_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block79) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block79,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inl True.intro)))
theorem rightBlock80_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block80) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block80,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))
theorem rightBlock81_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block81) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block81,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))
theorem rightBlock82_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block82) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block82,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))
theorem rightBlock83_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block83) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block83,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))
theorem rightBlock84_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block84) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block84,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))
theorem rightBlock85_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block85) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block85,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))
theorem rightBlock86_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block86) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block86,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))
theorem rightBlock87_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block87) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block87,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))
theorem rightBlock88_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block88) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block88,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))
theorem rightBlock89_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block89) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block89,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))
theorem rightBlock90_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block90) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block90,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))
theorem rightBlock91_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block91) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block91,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))
theorem rightBlock92_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block92) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block92,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))
theorem rightBlock93_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block93) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block93,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))
theorem rightBlock94_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block94) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block94,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))
theorem rightBlock95_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block95) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block95,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))
theorem rightBlock96_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block96) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block96,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))
theorem rightBlock97_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block97) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block97,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))
theorem rightBlock98_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block98) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block98,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))
theorem rightBlock99_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block99) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block99,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))
theorem rightBlock100_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block100) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block100,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))
theorem rightBlock101_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block101) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block101,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))
theorem rightBlock102_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block102) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block102,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))
theorem rightBlock103_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block103) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block103,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))
theorem rightBlock104_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block104) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block104,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))
theorem rightBlock105_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block105) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block105,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))
theorem rightBlock106_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block106) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block106,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))
theorem rightBlock107_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block107) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block107,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))
theorem rightBlock108_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block108) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block108,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))
theorem rightBlock109_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block109) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block109,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))
theorem rightBlock110_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block110) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block110,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))
theorem rightBlock111_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block111) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block111,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))
theorem rightBlock112_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block112) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block112,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))
theorem rightBlock113_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block113) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block113,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))
theorem rightBlock114_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block114) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block114,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))
theorem rightBlock115_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block115) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block115,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))
theorem rightBlock116_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block116) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block116,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))
theorem rightBlock117_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block117) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block117,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))
theorem rightBlock118_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block118) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block118,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock119_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block119) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block119,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock120_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block120) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block120,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock121_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block121) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block121,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock122_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block122) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block122,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock123_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block123) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block123,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock124_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block124) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block124,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock125_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block125) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block125,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock126_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block126) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block126,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock127_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block127) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block127,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock128_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block128) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block128,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock129_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block129) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block129,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock130_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block130) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block130,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock131_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block131) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block131,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock132_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block132) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block132,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock133_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block133) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block133,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock134_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block134) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block134,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock135_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block135) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block135,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock136_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block136) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block136,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock137_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block137) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block137,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock138_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block138) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block138,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock139_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block139) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block139,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock140_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block140) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block140,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock141_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block141) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block141,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock142_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block142) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block142,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock143_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block143) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block143,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock144_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block144) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block144,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock145_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block145) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block145,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock146_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block146) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block146,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock147_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block147) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block147,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock148_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block148) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block148,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock149_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block149) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block149,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock150_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block150) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block150,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock151_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block151) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block151,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock152_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block152) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block152,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock153_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block153) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block153,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock154_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block154) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block154,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock155_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block155) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block155,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock156_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block156) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block156,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rightBlock157_subset {r : ResidualCell.Row} (hr : r∈ReferenceResiduals.block157) : r∈rightRows := by
  rw [rightRows_blocks]
  apply List.mem_flatten.mpr
  refine ⟨ReferenceResiduals.block157,?_,hr⟩
  simp only [rightBlocks,List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
end chebyshev2.Certificates.Compact.ReferenceTrajectory
