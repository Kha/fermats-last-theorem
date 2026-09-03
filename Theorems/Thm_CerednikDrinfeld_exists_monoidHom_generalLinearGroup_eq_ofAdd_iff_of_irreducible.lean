import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_monoidHom_generalLinearGroup_eq_ofAdd_iff_of_irreducible

set_option autoImplicit false

theorem CerednikDrinfeld.exists_monoidHom_generalLinearGroup_eq_ofAdd_iff_of_irreducible
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (m : Type) [Fintype m] [DecidableEq m] :
    ∃ vdet : Matrix.GeneralLinearGroup m K₀ →* Multiplicative ℤ,
      ∀ (g : Matrix.GeneralLinearGroup m K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
        ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_monoidHom_generalLinearGroup_eq_ofAdd_iff_of_irreducible.solution
