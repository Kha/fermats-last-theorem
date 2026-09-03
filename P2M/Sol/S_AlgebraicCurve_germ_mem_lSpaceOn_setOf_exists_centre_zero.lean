import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
namespace P2MW.S_AlgebraicCurve_germ_mem_lSpaceOn_setOf_exists_centre_zero

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] (U : C.Opens) (hU : genericPoint C ∈ U) (t : Γ(C, U)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    C.presheaf.germ U (genericPoint C) hU t ∈
      lSpaceOn {v : Place k C.functionField | ∃ z : C, z ∈ U ∧
        (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField) := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  show C.presheaf.germ U (genericPoint C) hU t ∈ lSpaceOn _ (0 : Divisor k C.functionField)
  rw [AlgebraicCurve.mem_lSpaceOn_iff]
  rintro v ⟨z, hzU, hz⟩
  have key : algebraMap (C.presheaf.stalk z) C.functionField (C.presheaf.germ U z hzU t) =
      C.presheaf.germ U (genericPoint C) hU t := by
    change (C.presheaf.germ U z hzU ≫ C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)).hom t = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
  have h1 := (hz (C.presheaf.germ U z hzU t)).1
  rw [key] at h1
  simpa using h1
