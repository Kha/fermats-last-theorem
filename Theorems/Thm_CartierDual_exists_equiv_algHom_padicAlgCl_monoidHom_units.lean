import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_CartierDual_exists_equiv_algHom_padicAlgCl_monoidHom_units

set_option autoImplicit false

open scoped PadicInt

theorem CartierDual.exists_equiv_algHom_padicAlgCl_monoidHom_units
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H] :
    ∃ d : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p) ≃
        (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) →* (PadicAlgCl p)ˣ),
      (∀ φ ψ, d (φ * ψ) = d φ * d ψ) ∧
      (∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (φ φ' : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p)),
        (∀ y, φ' y = σ (φ y)) →
        ∀ (f f' : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x, f' x = σ (f x)) →
          ((d φ' f' : (PadicAlgCl p)ˣ) : PadicAlgCl p) = σ ((d φ f : (PadicAlgCl p)ˣ) : PadicAlgCl p)) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_exists_equiv_algHom_padicAlgCl_monoidHom_units.solution
