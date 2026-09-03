import Mathlib
import Definitions.Def_NumberField_RayCharacterData
import P2M.Util
import P2M.Sol.S_NumberField_exists_isGaussDatum

set_option autoImplicit false

open NumberField Deep.NTSupply

theorem NumberField.exists_isGaussDatum
    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) :
    ∃ y : K, M4aP2.IsGaussDatum K 𝔣 χ y := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_isGaussDatum.solution
