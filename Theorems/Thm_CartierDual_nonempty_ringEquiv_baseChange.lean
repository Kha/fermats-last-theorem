import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_CartierDual_nonempty_ringEquiv_baseChange

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.nonempty_ringEquiv_baseChange
    (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S]
    (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
    [Coalgebra.IsCocomm R A] :
    Nonempty (CartierDual S (S ⊗[R] A) ≃+* S ⊗[R] CartierDual R A) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_nonempty_ringEquiv_baseChange.solution
