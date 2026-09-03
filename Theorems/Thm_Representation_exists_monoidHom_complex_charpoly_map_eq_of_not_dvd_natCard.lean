import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard

set_option autoImplicit false

open Polynomial
open scoped MatrixGroups

theorem Representation.exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard
    (G : Type) [Group G] [Finite G]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ Nat.card G)
    (k : Type) [Field k] [Finite k] [CharP k ℓ]
    (n m : ℕ) (hm : 0 < m) (hℓm : ¬ ℓ ∣ m) (hGm : ∀ g : G, g ^ m = 1)
    (S : Subalgebra ℤ ℂ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (hζS : ζ ∈ S) (φ : S →+* k)
    (ρbar : G →* GL (Fin n) k) :
    ∃ ρ : G →* GL (Fin n) ℂ, ∀ g : G, ∃ P : Polynomial S,
      P.map (algebraMap S ℂ) = ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly ∧
      P.map φ = ((ρbar g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard.solution
