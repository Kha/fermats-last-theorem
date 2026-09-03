import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top

theorem Submodule.eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) [IsAdicComplete I A] [IsHausdorff I M]
    (N : Submodule A M) (hN : N.FG) (h : N ⊔ I • ⊤ = ⊤) : N = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Submodule_eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top.solution
