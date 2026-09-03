import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_M4aHerbrand_IdeleGaloisDescent_ideleNorm_unitsAct

set_option autoImplicit false

open NumberField

theorem M4aHerbrand.IdeleGaloisDescent.ideleNorm_unitsAct
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L (D.unitsAct σ z) = NumberField.TateGlobal.ideleNorm L z := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_IdeleGaloisDescent_ideleNorm_unitsAct.solution
