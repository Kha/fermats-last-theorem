import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_localBox_inf

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

theorem Submodule.localBox_inf
    {D : Type*} [Ring D] [Algebra ℚ D] (Λ₁ Λ₂ : Submodule ℤ D)
    (h₁fg : Λ₁.FG) (h₁sp : Submodule.span ℚ (Λ₁ : Set D) = ⊤)
    (h₂fg : Λ₂.FG) (h₂sp : Submodule.span ℚ (Λ₂ : Set D) = ⊤)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox (Λ₁ ⊓ Λ₂) v = Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ₂ v := by p2m_exact_reverting @_root_.P2MW.S_Submodule_localBox_inf.solution
