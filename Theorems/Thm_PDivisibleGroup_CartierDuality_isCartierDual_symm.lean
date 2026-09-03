import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_isCartierDual_symm
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.isCartierDual_symm
    {R : Type} [CommRing R] {p h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G') :
    G'.IsCartierDual G := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_isCartierDual_symm.solution
