import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange

set_option autoImplicit false
open NumberField M4aHerbrand M4aHerbrand.GenuineDescent

theorem M4aHerbrand.IdeleGaloisDescent.unitsAct_map_genuineBaseChange
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
    (D : IdeleGaloisDescent (𝓞 F) E F) (D'' : IdeleGaloisDescent (𝓞 M) E M)
    (σ : M ≃ₐ[E] M) (x : (AdeleRing (𝓞 F) F)ˣ) :
    D''.unitsAct σ (Units.map (genuineBaseChange F M).β.toMonoidHom x) =
      Units.map (genuineBaseChange F M).β.toMonoidHom (D.unitsAct (AlgEquiv.restrictNormalHom F σ) x) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange.solution
