import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_HopfAlgebra_CartierDualMap
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_pair_comp_eq_pair_comp_cartierTranspose

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.CartierDuality.pair_comp_eq_pair_comp_cartierTranspose
    {R : Type} [CommRing R] {p h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (v : ℕ) (u : G.level v →ₐc[R] G.level v)
    (L : Type) [CommRing L] [Algebra R L]
    (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom f).comp (u : G.level v →ₐ[R] G.level v))) ψ =
      D.pair L v f (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom ψ).comp
        (((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] G'.level v).comp
          ((CartierDual.map u).comp (D.equiv v : G'.level v →ₐc[R] CartierDual R (G.level v))) :
            G'.level v →ₐ[R] G'.level v))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_pair_comp_eq_pair_comp_cartierTranspose.solution
