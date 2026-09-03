import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelP_BasisRing_exists_ringHom_basisData_map_eq

set_option autoImplicit false

universe u v

theorem ModularCurve.LevelP.BasisRing.exists_ringHom_basisData_map_eq
    {B : Type u} {A : Type v} [CommRing B] [CommRing A] (W : WeierstrassCurve B) (p : ℕ)
    (φ : B →+* A) (D : ModularCurve.LevelPData A)
    (hD : ModularCurve.IsLevelPStructure (W.map φ) p D) :
    ∃ ψ : ModularCurve.LevelP.BasisRing W p →+* A,
      ψ.comp (ModularCurve.LevelP.BasisRing.ofBase W p) = φ ∧
        (ModularCurve.LevelP.basisData W p).map ψ = D := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelP_BasisRing_exists_ringHom_basisData_map_eq.solution
