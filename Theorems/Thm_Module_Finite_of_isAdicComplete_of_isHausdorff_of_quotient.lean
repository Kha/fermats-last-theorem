import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Finite_of_isAdicComplete_of_isHausdorff_of_quotient

universe u v

theorem Module.Finite.of_isAdicComplete_of_isHausdorff_of_quotient
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type v) [AddCommGroup M] [Module R M] [IsHausdorff I M]
    (h : Module.Finite R (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Finite R M := by p2m_exact_reverting @_root_.P2MW.S_Module_Finite_of_isAdicComplete_of_isHausdorff_of_quotient.solution
