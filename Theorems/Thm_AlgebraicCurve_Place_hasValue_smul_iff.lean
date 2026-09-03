import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_hasValue_smul_iff

set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.Place.hasValue_smul_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (v : Place K F) (g : F) (a : K) :
    (σ • v).HasValue (σ g) a ↔ v.HasValue g a := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_hasValue_smul_iff.solution
