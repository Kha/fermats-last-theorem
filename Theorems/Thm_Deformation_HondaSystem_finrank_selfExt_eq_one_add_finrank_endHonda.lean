import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_HondaSelfExt
import P2M.Util
import P2M.Sol.S_Deformation_HondaSystem_finrank_selfExt_eq_one_add_finrank_endHonda

universe u v

theorem Deformation.HondaSystem.finrank_selfExt_eq_one_add_finrank_endHonda
    {k : Type u} [Field k] {D : Type v} [AddCommGroup D] [Module k D]
    [FiniteDimensional k D] {ℓ : k} (hℓ : ℓ = 0) (H : Deformation.HondaSystem ℓ D)
    (hD : Module.finrank k D = 2) (hL : Module.finrank k H.L = 1) :
    Module.finrank k H.selfExt = 1 + Module.finrank k H.endHonda := by p2m_exact_reverting @_root_.P2MW.S_Deformation_HondaSystem_finrank_selfExt_eq_one_add_finrank_endHonda.solution
