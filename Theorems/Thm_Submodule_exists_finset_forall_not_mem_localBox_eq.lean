import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_exists_finset_forall_not_mem_localBox_eq

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem Submodule.exists_finset_forall_not_mem_localBox_eq
    {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ₁ Λ₂ : Submodule ℤ D) (hfg₁ : Λ₁.FG) (hsp₁ : Submodule.span ℚ (Λ₁ : Set D) = ⊤)
    (hfg₂ : Λ₂.FG) (hsp₂ : Submodule.span ℚ (Λ₂ : Set D) = ⊤) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ v ∉ S,
      Submodule.localBox Λ₁ v = Submodule.localBox Λ₂ v := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_finset_forall_not_mem_localBox_eq.solution
