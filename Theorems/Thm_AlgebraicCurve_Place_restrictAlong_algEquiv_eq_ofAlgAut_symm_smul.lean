import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (hσ : σ.toAlgHom.toRingHom.IsIntegral) (v : Place K F) :
    v.restrictAlong σ.toAlgHom hσ = SemilinearAut.ofAlgAut σ.symm • v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul.solution
