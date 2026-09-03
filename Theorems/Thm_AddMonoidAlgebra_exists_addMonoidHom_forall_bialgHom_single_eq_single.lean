import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidAlgebra_exists_addMonoidHom_forall_bialgHom_single_eq_single

set_option autoImplicit false

theorem AddMonoidAlgebra.exists_addMonoidHom_forall_bialgHom_single_eq_single
    {S : Type} [CommRing S] [IsDomain S] (G : Type) [AddCommGroup G]
    (f : AddMonoidAlgebra S G →ₐc[S] AddMonoidAlgebra S G) :
    ∃ M : G →+ G, ∀ g : G, f (AddMonoidAlgebra.single g 1) = AddMonoidAlgebra.single (M g) 1 := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidAlgebra_exists_addMonoidHom_forall_bialgHom_single_eq_single.solution
