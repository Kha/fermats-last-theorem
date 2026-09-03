import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_M4aHerbrand_IdeleGaloisDescent_apply_unitsAct_eq_of_forall_mem_normOneIdeles
attribute [-simp] LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero

set_option autoImplicit false

open NumberField

theorem M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_eq_of_forall_mem_normOneIdeles
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {M : Type*} [CommGroup M] (ξ : (AdeleRing (𝓞 L) L)ˣ →* M)
    (h : ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, ξ (D.unitsAct σ z) = ξ z)
    (z : (AdeleRing (𝓞 L) L)ˣ) : ξ (D.unitsAct σ z) = ξ z := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_IdeleGaloisDescent_apply_unitsAct_eq_of_forall_mem_normOneIdeles.solution
