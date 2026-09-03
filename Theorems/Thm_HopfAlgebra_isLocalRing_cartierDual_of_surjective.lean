import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isLocalRing_cartierDual_of_surjective
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply

universe u v w

theorem HopfAlgebra.isLocalRing_cartierDual_of_surjective
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Bialgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (B : Type w) [CommRing B] [Bialgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]
    (π : A →ₐc[k] B) (hπ : Function.Surjective π) (hA : IsLocalRing (CartierDual k A)) :
    IsLocalRing (CartierDual k B) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isLocalRing_cartierDual_of_surjective.solution
