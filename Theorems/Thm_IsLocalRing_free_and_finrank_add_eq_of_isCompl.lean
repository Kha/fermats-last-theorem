import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_free_and_finrank_add_eq_of_isCompl

set_option autoImplicit false

theorem IsLocalRing.free_and_finrank_add_eq_of_isCompl
    {C : Type} [CommRing C] [IsLocalRing C] {N : Type} [AddCommGroup N] [Module C N]
    [Module.Finite C N] [Module.Free C N] (N0 N1 : Submodule C N) (h : IsCompl N0 N1) :
    Module.Free C N0 ∧ Module.Finite C N0 ∧ Module.Free C N1 ∧ Module.Finite C N1 ∧
      Module.finrank C N0 + Module.finrank C N1 = Module.finrank C N := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_free_and_finrank_add_eq_of_isCompl.solution
