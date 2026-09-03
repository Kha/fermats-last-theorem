import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_HopfAlgebra_CartierDualMap
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_transpose_comp_transition_eq_and_pair_comp_eq_pair_comp_transpose

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.transpose_comp_transition_eq_and_pair_comp_eq_pair_comp_transpose
    {R : Type} [CommRing R] {p h h' : ℕ}
    {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    {Γ Γ' : PDivisibleGroup R p h'} (E : Γ.CartierDuality Γ')
    (φ : ∀ v : ℕ, G.level v →ₐc[R] Γ.level v)
    (hφ : ∀ v : ℕ, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1))) :
    (∀ v : ℕ,
      (((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] G'.level v).comp
          ((CartierDual.map (φ v)).comp (E.equiv v : Γ'.level v →ₐc[R] CartierDual R (Γ.level v)))).comp
        (Γ'.transition v) =
      (G'.transition v).comp
        (((D.equiv (v + 1)).symm : CartierDual R (G.level (v + 1)) →ₐc[R] G'.level (v + 1)).comp
          ((CartierDual.map (φ (v + 1))).comp (E.equiv (v + 1) : Γ'.level (v + 1) →ₐc[R] CartierDual R (Γ.level (v + 1)))))) ∧
    ∀ (L : Type) [CommRing L] [Algebra R L] (v : ℕ) (x : Γ.Point L v) (y : G'.Point L v),
      D.pair L v (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : G.level v →ₐ[R] Γ.level v))) y =
        E.pair L v x (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp
          ((((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] G'.level v).comp
          ((CartierDual.map (φ v)).comp (E.equiv v : Γ'.level v →ₐc[R] CartierDual R (Γ.level v)))) :
            Γ'.level v →ₐ[R] G'.level v))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_transpose_comp_transition_eq_and_pair_comp_eq_pair_comp_transpose.solution
