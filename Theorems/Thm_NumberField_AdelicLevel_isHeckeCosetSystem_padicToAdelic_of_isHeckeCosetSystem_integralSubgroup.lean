import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_PadicHeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import P2M.Util
import P2M.Sol.S_NumberField_AdelicLevel_isHeckeCosetSystem_padicToAdelic_of_isHeckeCosetSystem_integralSubgroup

set_option autoImplicit false

theorem NumberField.AdelicLevel.isHeckeCosetSystem_padicToAdelic_of_isHeckeCosetSystem_integralSubgroup
    {N : ℕ} (hN : N ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    {ι : Type*} (α : ι → GL (Fin 2) ℚ_[ℓ])
    (hα : HeckeIntegralSeam.IsHeckeCosetSystem (LocalGL2.integralSubgroup ℤ_[ℓ] ℚ_[ℓ])
      (HeckeIntegralSeam.padicDiagP ℓ) α) :
    HeckeIntegralSeam.IsHeckeCosetSystem
      (NumberField.AdelicLevel.levelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel N) ⊓
        AutomorphicForm.finiteAdelicGL2Subgroup ℚ)
      (NumberField.AdelicLevel.heckeGen (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace ℓ))
      (fun i => AdelicDock.padicToAdelic ℓ (α i)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicLevel_isHeckeCosetSystem_padicToAdelic_of_isHeckeCosetSystem_integralSubgroup.solution
