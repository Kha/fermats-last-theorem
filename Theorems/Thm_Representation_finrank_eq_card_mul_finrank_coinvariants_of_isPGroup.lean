import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_finrank_eq_card_mul_finrank_coinvariants_of_isPGroup

set_option autoImplicit false

theorem Representation.finrank_eq_card_mul_finrank_coinvariants_of_isPGroup
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField 𝒪) p]
    {G : Type} [Group G] [Fintype G] (hG : IsPGroup p G)
    {P : Type} [AddCommGroup P] [Module 𝒪 P] [Module.Finite 𝒪 P] [Module.IsTorsionFree 𝒪 P]
    (ρ : Representation 𝒪 G P)
    (h0 : ∀ w : P, (∀ g : G, ρ g w = w) → ∃ m : P, ρ.norm m = w)
    (h1 : ∀ v : P, ρ.norm v = 0 → v ∈ Representation.Coinvariants.ker ρ) :
    Module.finrank 𝒪 P = Fintype.card G * Module.finrank 𝒪 (Representation.Coinvariants ρ) := by p2m_exact_reverting @_root_.P2MW.S_Representation_finrank_eq_card_mul_finrank_coinvariants_of_isPGroup.solution
