import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_HondaSelfExt
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_finrank_selfExt_le_finrank_endHonda_add_one

set_option autoImplicit false

universe u v

theorem Deformation.HondaSystem.finrank_selfExt_le_finrank_endHonda_add_one
    {k : Type u} [Field k] {D : Type v} [AddCommGroup D] [Module k D]
    [FiniteDimensional k D] {ℓ : k} (hℓ : ℓ = 0) (H : Deformation.HondaSystem ℓ D)
    (hD : Module.finrank k D = 2) :
    Module.finrank k H.selfExt ≤ Module.finrank k H.endHonda + 1 := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_finrank_selfExt_le_finrank_endHonda_add_one.solution
