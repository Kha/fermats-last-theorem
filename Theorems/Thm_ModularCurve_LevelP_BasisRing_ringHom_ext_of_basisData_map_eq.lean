import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelP_BasisRing_ringHom_ext_of_basisData_map_eq

set_option autoImplicit false

open ModularCurve ModularCurve.LevelP

theorem ModularCurve.LevelP.BasisRing.ringHom_ext_of_basisData_map_eq
    {B : Type*} {A : Type*} [CommRing B] [CommRing A] (W : WeierstrassCurve B) (p : ℕ)
    (φ : B →+* A) (ψ ψ' : BasisRing W p →+* A)
    (hψ : ψ.comp (BasisRing.ofBase W p) = φ) (hψ' : ψ'.comp (BasisRing.ofBase W p) = φ)
    (h : (basisData W p).map ψ = (basisData W p).map ψ') :
    ψ = ψ' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelP_BasisRing_ringHom_ext_of_basisData_map_eq.solution
