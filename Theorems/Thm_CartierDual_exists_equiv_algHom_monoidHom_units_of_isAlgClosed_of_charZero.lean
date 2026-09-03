import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_CartierDual_exists_equiv_algHom_monoidHom_units_of_isAlgClosed_of_charZero

set_option autoImplicit false

theorem CartierDual.exists_equiv_algHom_monoidHom_units_of_isAlgClosed_of_charZero
    (O : Type) [CommRing O]
    (H : Type) [CommRing H] [HopfAlgebra O H] [Module.Finite O H] [Module.Free O H] [Coalgebra.IsCocomm O H]
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra O L] :
    ∃ d : WithConv (CartierDual O H →ₐ[O] L) ≃ (WithConv (H →ₐ[O] L) →* Lˣ),
      (∀ φ ψ, d (φ * ψ) = d φ * d ψ) ∧
      (∀ (σ : L ≃ₐ[O] L) (φ φ' : WithConv (CartierDual O H →ₐ[O] L)),
        (∀ y, φ' y = σ (φ y)) →
        ∀ (f f' : WithConv (H →ₐ[O] L)), (∀ x, f' x = σ (f x)) →
          ((d φ' f' : Lˣ) : L) = σ ((d φ f : Lˣ) : L)) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_exists_equiv_algHom_monoidHom_units_of_isAlgClosed_of_charZero.solution
