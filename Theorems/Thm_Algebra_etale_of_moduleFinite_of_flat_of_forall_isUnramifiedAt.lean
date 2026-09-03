import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_etale_of_moduleFinite_of_flat_of_forall_isUnramifiedAt

set_option autoImplicit false

universe u

theorem Algebra.etale_of_moduleFinite_of_flat_of_forall_isUnramifiedAt
    (O : Type u) [CommRing O] [IsNoetherianRing O] (C : Type u) [CommRing C] [Algebra O C] [Module.Finite O C] [Module.Flat O C]
    (h : ∀ (Q : Ideal C) [Q.IsPrime], Algebra.IsUnramifiedAt O Q) :
    Algebra.Etale O C := by p2m_exact_reverting @_root_.P2MW.S_Algebra_etale_of_moduleFinite_of_flat_of_forall_isUnramifiedAt.solution
