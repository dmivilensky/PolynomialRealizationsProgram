import polyak.CertifiedExamples.Trigonometry

/-! Generated mathematical proposals; every bound is checked by the ordinary kernel. -/
namespace polyak.Certificates.PartII.Trigonometry
open CertifiedExamples.Trigonometry

theorem sin_13_0_bounds :
    (((-1/100000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*0/13) ∧
    Real.sin (2*Real.pi*0/13) ≤ (((1/50000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*0/13) 32 (-1/100000000000000) (1/50000000000000) (by kernel_decide)
  have he : (((2*0/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*0/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_13_0_bounds :
    (((99999999999999/100000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*0/13) ∧
    Real.cos (2*Real.pi*0/13) ≤ (((50000000000001/50000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*0/13) 32 (99999999999999/100000000000000) (50000000000001/50000000000000) (by kernel_decide)
  have he : (((2*0/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*0/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_3_1_bounds :
    (((43301270189221/50000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*1/3) ∧
    Real.sin (2*Real.pi*1/3) ≤ (((17320508075689/20000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*1/3) 32 (43301270189221/50000000000000) (17320508075689/20000000000000) (by kernel_decide)
  have he : (((2*1/3) : ℚ) : ℝ)*Real.pi = 2*Real.pi*1/3 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_3_1_bounds :
    (((-25000000000001/50000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*1/3) ∧
    Real.cos (2*Real.pi*1/3) ≤ (((-49999999999999/100000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*1/3) 32 (-25000000000001/50000000000000) (-49999999999999/100000000000000) (by kernel_decide)
  have he : (((2*1/3) : ℚ) : ℝ)*Real.pi = 2*Real.pi*1/3 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_4_1_bounds :
    (((99999999999999/100000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*1/4) ∧
    Real.sin (2*Real.pi*1/4) ≤ (((50000000000001/50000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*1/4) 32 (99999999999999/100000000000000) (50000000000001/50000000000000) (by kernel_decide)
  have he : (((2*1/4) : ℚ) : ℝ)*Real.pi = 2*Real.pi*1/4 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_4_1_bounds :
    (((-1/100000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*1/4) ∧
    Real.cos (2*Real.pi*1/4) ≤ (((1/50000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*1/4) 32 (-1/100000000000000) (1/50000000000000) (by kernel_decide)
  have he : (((2*1/4) : ℚ) : ℝ)*Real.pi = 2*Real.pi*1/4 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_5_1_bounds :
    (((47552825814757/50000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*1/5) ∧
    Real.sin (2*Real.pi*1/5) ≤ (((95105651629517/100000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*1/5) 32 (47552825814757/50000000000000) (95105651629517/100000000000000) (by kernel_decide)
  have he : (((2*1/5) : ℚ) : ℝ)*Real.pi = 2*Real.pi*1/5 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_5_1_bounds :
    (((30901699437493/100000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*1/5) ∧
    Real.cos (2*Real.pi*1/5) ≤ (((3862712429687/12500000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*1/5) 32 (30901699437493/100000000000000) (3862712429687/12500000000000) (by kernel_decide)
  have he : (((2*1/5) : ℚ) : ℝ)*Real.pi = 2*Real.pi*1/5 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_13_1_bounds :
    (((74355707527/160000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*1/13) ∧
    Real.sin (2*Real.pi*1/13) ≤ (((23236158602189/50000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*1/13) 32 (74355707527/160000000000) (23236158602189/50000000000000) (by kernel_decide)
  have he : (((2*1/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*1/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_13_1_bounds :
    (((88545602565319/100000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*1/13) ∧
    Real.cos (2*Real.pi*1/13) ≤ (((44272801282661/50000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*1/13) 32 (88545602565319/100000000000000) (44272801282661/50000000000000) (by kernel_decide)
  have he : (((2*1/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*1/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_5_2_bounds :
    (((29389262614623/50000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*2/5) ∧
    Real.sin (2*Real.pi*2/5) ≤ (((58778525229249/100000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*2/5) 32 (29389262614623/50000000000000) (58778525229249/100000000000000) (by kernel_decide)
  have he : (((2*2/5) : ℚ) : ℝ)*Real.pi = 2*Real.pi*2/5 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_5_2_bounds :
    (((-10112712429687/12500000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*2/5) ∧
    Real.cos (2*Real.pi*2/5) ≤ (((-80901699437493/100000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*2/5) 32 (-10112712429687/12500000000000) (-80901699437493/100000000000000) (by kernel_decide)
  have he : (((2*2/5) : ℚ) : ℝ)*Real.pi = 2*Real.pi*2/5 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_13_2_bounds :
    (((20574596647341/25000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*2/13) ∧
    Real.sin (2*Real.pi*2/13) ≤ (((82298386589367/100000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*2/13) 32 (20574596647341/25000000000000) (82298386589367/100000000000000) (by kernel_decide)
  have he : (((2*2/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*2/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_13_2_bounds :
    (((28403237336557/50000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*2/13) ∧
    Real.cos (2*Real.pi*2/13) ≤ (((56806474673117/100000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*2/13) 32 (28403237336557/50000000000000) (56806474673117/100000000000000) (by kernel_decide)
  have he : (((2*2/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*2/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_13_3_bounds :
    (((24817721852451/25000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*3/13) ∧
    Real.sin (2*Real.pi*3/13) ≤ (((99270887409807/100000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*3/13) 32 (24817721852451/25000000000000) (99270887409807/100000000000000) (by kernel_decide)
  have he : (((2*3/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*3/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_13_3_bounds :
    (((12053668025531/100000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*3/13) ∧
    Real.cos (2*Real.pi*3/13) ≤ (((6026834012767/50000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*3/13) 32 (12053668025531/100000000000000) (6026834012767/50000000000000) (by kernel_decide)
  have he : (((2*3/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*3/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_18_3_bounds :
    (((43301270189221/50000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*3/18) ∧
    Real.sin (2*Real.pi*3/18) ≤ (((17320508075689/20000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*3/18) 32 (43301270189221/50000000000000) (17320508075689/20000000000000) (by kernel_decide)
  have he : (((2*3/18) : ℚ) : ℝ)*Real.pi = 2*Real.pi*3/18 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_18_3_bounds :
    (((24999999999999/50000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*3/18) ∧
    Real.cos (2*Real.pi*3/18) ≤ (((50000000000001/100000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*3/18) 32 (24999999999999/50000000000000) (50000000000001/100000000000000) (by kernel_decide)
  have he : (((2*3/18) : ℚ) : ℝ)*Real.pi = 2*Real.pi*3/18 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_21_3_bounds :
    (((78183148246801/100000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*3/21) ∧
    Real.sin (2*Real.pi*3/21) ≤ (((19545787061701/25000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*3/21) 32 (78183148246801/100000000000000) (19545787061701/25000000000000) (by kernel_decide)
  have he : (((2*3/21) : ℚ) : ℝ)*Real.pi = 2*Real.pi*3/21 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_21_3_bounds :
    (((3896811261617/6250000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*3/21) ∧
    Real.cos (2*Real.pi*3/21) ≤ (((498791841487/800000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*3/21) 32 (3896811261617/6250000000000) (498791841487/800000000000) (by kernel_decide)
  have he : (((2*3/21) : ℚ) : ℝ)*Real.pi = 2*Real.pi*3/21 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_13_4_bounds :
    (((4675081213427/5000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*4/13) ∧
    Real.sin (2*Real.pi*4/13) ≤ (((93501624268543/100000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*4/13) 32 (4675081213427/5000000000000) (93501624268543/100000000000000) (by kernel_decide)
  have he : (((2*4/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*4/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_13_4_bounds :
    (((-7092097740851/20000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*4/13) ∧
    Real.cos (2*Real.pi*4/13) ≤ (((-8865122176063/25000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*4/13) 32 (-7092097740851/20000000000000) (-8865122176063/25000000000000) (by kernel_decide)
  have he : (((2*4/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*4/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_18_4_bounds :
    (((98480775301219/100000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*4/18) ∧
    Real.sin (2*Real.pi*4/18) ≤ (((49240387650611/50000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*4/18) 32 (98480775301219/100000000000000) (49240387650611/50000000000000) (by kernel_decide)
  have he : (((2*4/18) : ℚ) : ℝ)*Real.pi = 2*Real.pi*4/18 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_18_4_bounds :
    (((4341204441673/25000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*4/18) ∧
    Real.cos (2*Real.pi*4/18) ≤ (((3472963553339/20000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*4/18) 32 (4341204441673/25000000000000) (3472963553339/20000000000000) (by kernel_decide)
  have he : (((2*4/18) : ℚ) : ℝ)*Real.pi = 2*Real.pi*4/18 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_21_4_bounds :
    (((93087374864419/100000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*4/21) ∧
    Real.sin (2*Real.pi*4/21) ≤ (((46543687432211/50000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*4/21) 32 (93087374864419/100000000000000) (46543687432211/50000000000000) (by kernel_decide)
  have he : (((2*4/21) : ℚ) : ℝ)*Real.pi = 2*Real.pi*4/21 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_21_4_bounds :
    (((18267051218319/50000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*4/21) ∧
    Real.cos (2*Real.pi*4/21) ≤ (((36534102436641/100000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*4/21) 32 (18267051218319/50000000000000) (36534102436641/100000000000000) (by kernel_decide)
  have he : (((2*4/21) : ℚ) : ℝ)*Real.pi = 2*Real.pi*4/21 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_13_5_bounds :
    (((33156132912039/50000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*5/13) ∧
    Real.sin (2*Real.pi*5/13) ≤ (((66312265824081/100000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*5/13) 32 (33156132912039/50000000000000) (66312265824081/100000000000000) (by kernel_decide)
  have he : (((2*5/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*5/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_13_5_bounds :
    (((-9356384352139/12500000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*5/13) ∧
    Real.cos (2*Real.pi*5/13) ≤ (((-74851074817109/100000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*5/13) 32 (-9356384352139/12500000000000) (-74851074817109/100000000000000) (by kernel_decide)
  have he : (((2*5/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*5/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_21_5_bounds :
    (((99720379718117/100000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*5/21) ∧
    Real.sin (2*Real.pi*5/21) ≤ (((2493009492953/2500000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*5/21) 32 (99720379718117/100000000000000) (2493009492953/2500000000000) (by kernel_decide)
  have he : (((2*5/21) : ℚ) : ℝ)*Real.pi = 2*Real.pi*5/21 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_21_5_bounds :
    (((7473009358641/100000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*5/21) ∧
    Real.cos (2*Real.pi*5/21) ≤ (((1868252339661/25000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*5/21) 32 (7473009358641/100000000000000) (1868252339661/25000000000000) (by kernel_decide)
  have he : (((2*5/21) : ℚ) : ℝ)*Real.pi = 2*Real.pi*5/21 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_13_6_bounds :
    (((11965783214377/50000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*6/13) ∧
    Real.sin (2*Real.pi*6/13) ≤ (((23931566428757/100000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*6/13) 32 (11965783214377/50000000000000) (23931566428757/100000000000000) (by kernel_decide)
  have he : (((2*6/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*6/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_13_6_bounds :
    (((-97094181742607/100000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*6/13) ∧
    Real.cos (2*Real.pi*6/13) ≤ (((-24273545435651/25000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*6/13) 32 (-97094181742607/100000000000000) (-24273545435651/25000000000000) (by kernel_decide)
  have he : (((2*6/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*6/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_13_7_bounds :
    (((-23931566428757/100000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*7/13) ∧
    Real.sin (2*Real.pi*7/13) ≤ (((-11965783214377/50000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*7/13) 32 (-23931566428757/100000000000000) (-11965783214377/50000000000000) (by kernel_decide)
  have he : (((2*7/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*7/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_13_7_bounds :
    (((-97094181742607/100000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*7/13) ∧
    Real.cos (2*Real.pi*7/13) ≤ (((-24273545435651/25000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*7/13) 32 (-97094181742607/100000000000000) (-24273545435651/25000000000000) (by kernel_decide)
  have he : (((2*7/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*7/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_13_8_bounds :
    (((-66312265824081/100000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*8/13) ∧
    Real.sin (2*Real.pi*8/13) ≤ (((-33156132912039/50000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*8/13) 32 (-66312265824081/100000000000000) (-33156132912039/50000000000000) (by kernel_decide)
  have he : (((2*8/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*8/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_13_8_bounds :
    (((-9356384352139/12500000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*8/13) ∧
    Real.cos (2*Real.pi*8/13) ≤ (((-74851074817109/100000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*8/13) 32 (-9356384352139/12500000000000) (-74851074817109/100000000000000) (by kernel_decide)
  have he : (((2*8/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*8/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_13_9_bounds :
    (((-93501624268543/100000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*9/13) ∧
    Real.sin (2*Real.pi*9/13) ≤ (((-4675081213427/5000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*9/13) 32 (-93501624268543/100000000000000) (-4675081213427/5000000000000) (by kernel_decide)
  have he : (((2*9/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*9/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_13_9_bounds :
    (((-7092097740851/20000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*9/13) ∧
    Real.cos (2*Real.pi*9/13) ≤ (((-8865122176063/25000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*9/13) 32 (-7092097740851/20000000000000) (-8865122176063/25000000000000) (by kernel_decide)
  have he : (((2*9/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*9/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_13_10_bounds :
    (((-99270887409807/100000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*10/13) ∧
    Real.sin (2*Real.pi*10/13) ≤ (((-24817721852451/25000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*10/13) 32 (-99270887409807/100000000000000) (-24817721852451/25000000000000) (by kernel_decide)
  have he : (((2*10/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*10/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_13_10_bounds :
    (((12053668025531/100000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*10/13) ∧
    Real.cos (2*Real.pi*10/13) ≤ (((6026834012767/50000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*10/13) 32 (12053668025531/100000000000000) (6026834012767/50000000000000) (by kernel_decide)
  have he : (((2*10/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*10/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_13_11_bounds :
    (((-82298386589367/100000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*11/13) ∧
    Real.sin (2*Real.pi*11/13) ≤ (((-20574596647341/25000000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*11/13) 32 (-82298386589367/100000000000000) (-20574596647341/25000000000000) (by kernel_decide)
  have he : (((2*11/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*11/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_13_11_bounds :
    (((28403237336557/50000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*11/13) ∧
    Real.cos (2*Real.pi*11/13) ≤ (((56806474673117/100000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*11/13) 32 (28403237336557/50000000000000) (56806474673117/100000000000000) (by kernel_decide)
  have he : (((2*11/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*11/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem sin_13_12_bounds :
    (((-23236158602189/50000000000000) : ℚ) : ℝ) ≤ Real.sin (2*Real.pi*12/13) ∧
    Real.sin (2*Real.pi*12/13) ≤ (((-74355707527/160000000000) : ℚ) : ℝ) := by
  have h := sin_bounds (2*12/13) 32 (-23236158602189/50000000000000) (-74355707527/160000000000) (by kernel_decide)
  have he : (((2*12/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*12/13 := by push_cast; ring
  rw [he] at h
  exact h

theorem cos_13_12_bounds :
    (((88545602565319/100000000000000) : ℚ) : ℝ) ≤ Real.cos (2*Real.pi*12/13) ∧
    Real.cos (2*Real.pi*12/13) ≤ (((44272801282661/50000000000000) : ℚ) : ℝ) := by
  have h := cos_bounds (2*12/13) 32 (88545602565319/100000000000000) (44272801282661/50000000000000) (by kernel_decide)
  have he : (((2*12/13) : ℚ) : ℝ)*Real.pi = 2*Real.pi*12/13 := by push_cast; ring
  rw [he] at h
  exact h

def cos13Interval : Fin 13 → LeanCert.Core.IntervalRat :=
  ![⟨(99999999999999/100000000000000),(50000000000001/50000000000000),by norm_num⟩,⟨(88545602565319/100000000000000),(44272801282661/50000000000000),by norm_num⟩,⟨(28403237336557/50000000000000),(56806474673117/100000000000000),by norm_num⟩,⟨(12053668025531/100000000000000),(6026834012767/50000000000000),by norm_num⟩,⟨(-7092097740851/20000000000000),(-8865122176063/25000000000000),by norm_num⟩,⟨(-9356384352139/12500000000000),(-74851074817109/100000000000000),by norm_num⟩,⟨(-97094181742607/100000000000000),(-24273545435651/25000000000000),by norm_num⟩,⟨(-97094181742607/100000000000000),(-24273545435651/25000000000000),by norm_num⟩,⟨(-9356384352139/12500000000000),(-74851074817109/100000000000000),by norm_num⟩,⟨(-7092097740851/20000000000000),(-8865122176063/25000000000000),by norm_num⟩,⟨(12053668025531/100000000000000),(6026834012767/50000000000000),by norm_num⟩,⟨(28403237336557/50000000000000),(56806474673117/100000000000000),by norm_num⟩,⟨(88545602565319/100000000000000),(44272801282661/50000000000000),by norm_num⟩]

theorem cos13_mem (j : Fin 13) :
    Real.cos (2*Real.pi*j.val/13) ∈ cos13Interval j := by
  fin_cases j
  · simpa [cos13Interval,LeanCert.Core.IntervalRat.mem_def] using cos_13_0_bounds
  · simpa [cos13Interval,LeanCert.Core.IntervalRat.mem_def] using cos_13_1_bounds
  · simpa [cos13Interval,LeanCert.Core.IntervalRat.mem_def] using cos_13_2_bounds
  · simpa [cos13Interval,LeanCert.Core.IntervalRat.mem_def] using cos_13_3_bounds
  · simpa [cos13Interval,LeanCert.Core.IntervalRat.mem_def] using cos_13_4_bounds
  · simpa [cos13Interval,LeanCert.Core.IntervalRat.mem_def] using cos_13_5_bounds
  · simpa [cos13Interval,LeanCert.Core.IntervalRat.mem_def] using cos_13_6_bounds
  · simpa [cos13Interval,LeanCert.Core.IntervalRat.mem_def] using cos_13_7_bounds
  · simpa [cos13Interval,LeanCert.Core.IntervalRat.mem_def] using cos_13_8_bounds
  · simpa [cos13Interval,LeanCert.Core.IntervalRat.mem_def] using cos_13_9_bounds
  · simpa [cos13Interval,LeanCert.Core.IntervalRat.mem_def] using cos_13_10_bounds
  · simpa [cos13Interval,LeanCert.Core.IntervalRat.mem_def] using cos_13_11_bounds
  · simpa [cos13Interval,LeanCert.Core.IntervalRat.mem_def] using cos_13_12_bounds

def sin13Interval : Fin 13 → LeanCert.Core.IntervalRat :=
  ![⟨(-1/100000000000000),(1/50000000000000),by norm_num⟩,⟨(74355707527/160000000000),(23236158602189/50000000000000),by norm_num⟩,⟨(20574596647341/25000000000000),(82298386589367/100000000000000),by norm_num⟩,⟨(24817721852451/25000000000000),(99270887409807/100000000000000),by norm_num⟩,⟨(4675081213427/5000000000000),(93501624268543/100000000000000),by norm_num⟩,⟨(33156132912039/50000000000000),(66312265824081/100000000000000),by norm_num⟩,⟨(11965783214377/50000000000000),(23931566428757/100000000000000),by norm_num⟩,⟨(-23931566428757/100000000000000),(-11965783214377/50000000000000),by norm_num⟩,⟨(-66312265824081/100000000000000),(-33156132912039/50000000000000),by norm_num⟩,⟨(-93501624268543/100000000000000),(-4675081213427/5000000000000),by norm_num⟩,⟨(-99270887409807/100000000000000),(-24817721852451/25000000000000),by norm_num⟩,⟨(-82298386589367/100000000000000),(-20574596647341/25000000000000),by norm_num⟩,⟨(-23236158602189/50000000000000),(-74355707527/160000000000),by norm_num⟩]

theorem sin13_mem (j : Fin 13) :
    Real.sin (2*Real.pi*j.val/13) ∈ sin13Interval j := by
  fin_cases j
  · simpa [sin13Interval,LeanCert.Core.IntervalRat.mem_def] using sin_13_0_bounds
  · simpa [sin13Interval,LeanCert.Core.IntervalRat.mem_def] using sin_13_1_bounds
  · simpa [sin13Interval,LeanCert.Core.IntervalRat.mem_def] using sin_13_2_bounds
  · simpa [sin13Interval,LeanCert.Core.IntervalRat.mem_def] using sin_13_3_bounds
  · simpa [sin13Interval,LeanCert.Core.IntervalRat.mem_def] using sin_13_4_bounds
  · simpa [sin13Interval,LeanCert.Core.IntervalRat.mem_def] using sin_13_5_bounds
  · simpa [sin13Interval,LeanCert.Core.IntervalRat.mem_def] using sin_13_6_bounds
  · simpa [sin13Interval,LeanCert.Core.IntervalRat.mem_def] using sin_13_7_bounds
  · simpa [sin13Interval,LeanCert.Core.IntervalRat.mem_def] using sin_13_8_bounds
  · simpa [sin13Interval,LeanCert.Core.IntervalRat.mem_def] using sin_13_9_bounds
  · simpa [sin13Interval,LeanCert.Core.IntervalRat.mem_def] using sin_13_10_bounds
  · simpa [sin13Interval,LeanCert.Core.IntervalRat.mem_def] using sin_13_11_bounds
  · simpa [sin13Interval,LeanCert.Core.IntervalRat.mem_def] using sin_13_12_bounds

end polyak.Certificates.PartII.Trigonometry
