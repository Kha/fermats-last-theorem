import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_HondaSelfExt
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_finrank_selfExt_eq_finrank_endHonda_of_L_eq_top

set_option autoImplicit false

universe u v

theorem Deformation.HondaSystem.finrank_selfExt_eq_finrank_endHonda_of_L_eq_top
    {k : Type u} [Field k] {D : Type v} [AddCommGroup D] [Module k D]
    [FiniteDimensional k D] {ℓ : k} (hℓ : ℓ = 0) (H : Deformation.HondaSystem ℓ D)
    (hL : H.L = ⊤) :
    Module.finrank k H.selfExt = Module.finrank k H.endHonda := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_finrank_selfExt_eq_finrank_endHonda_of_L_eq_top.solution
