import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_units_monoidHom_residue_eq_of_injective_of_card_eq_prime_pow

theorem ValuationSubring.exists_units_monoidHom_residue_eq_of_injective_of_card_eq_prime_pow
    (p : ℕ) [Fact p.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    {O : Type*} [CommRing O] (i : O →+* ↥P) (hinj : Function.Injective i)
    (hO : ∀ y : AlgebraicClosure ℚ, y ∈ P → (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ y = y) →
      ∃ x : O, ((i x : ↥P) : AlgebraicClosure ℚ) = y)
    (F : Type*) [Field F] [Fintype F] (s : ℕ) (hF : Fintype.card F = p ^ s) :
    ∃ (χ : Fˣ →* Oˣ) (ι₀ : F →+* IsLocalRing.ResidueField ↥P),
      ∀ l : Fˣ, IsLocalRing.residue ↥P (i ((χ l : Oˣ) : O)) = ι₀ l := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_units_monoidHom_residue_eq_of_injective_of_card_eq_prime_pow.solution
