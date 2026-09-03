import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_CartierDual_isLocalRing_and_isLocalRing_cartierDual_of_bialgHom_surjective_univ

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem CartierDual.isLocalRing_and_isLocalRing_cartierDual_of_bialgHom_surjective_univ
    (k : Type u) [Field k] (B : Type v) (B₁ : Type w) [CommRing B] [Bialgebra k B] [CommRing B₁] [Bialgebra k B₁]
    [Module.Finite k B] [Module.Finite k B₁] [Coalgebra.IsCocomm k B] [Coalgebra.IsCocomm k B₁]
    (π : B →ₐc[k] B₁) (hπ : Function.Surjective π)
    (hloc : IsLocalRing B) (hdual : IsLocalRing (CartierDual k B)) [Nontrivial B₁] :
    IsLocalRing B₁ ∧ IsLocalRing (CartierDual k B₁) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_isLocalRing_and_isLocalRing_cartierDual_of_bialgHom_surjective_univ.solution
