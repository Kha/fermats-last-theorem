import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_dualWhittakerFn3

set_option autoImplicit false

open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_dualWhittakerFn3
    {A : Type*} [CommRing A] {R : Type*} [CommRing R] (ψ : AddChar A R)
    (W : GL (Fin 3) A → R) (_hW : IsGL3PsiWhittakerFn ψ W) :
    IsGL3PsiWhittakerFn ψ⁻¹ (dualWhittakerFn3 W) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_dualWhittakerFn3.solution
