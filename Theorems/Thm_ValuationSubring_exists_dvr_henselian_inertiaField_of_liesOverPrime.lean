import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_dvr_henselian_inertiaField_of_liesOverPrime
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

theorem ValuationSubring.exists_dvr_henselian_inertiaField_of_liesOverPrime
    (ℓ : ℕ) (hℓ : ℓ.Prime) (B : ValuationSubring (AlgebraicClosure ℚ)) (hBℓ : B.LiesOverPrime ℓ) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : HenselianLocalRing O)
      (_ : IsAlgClosed (IsLocalRing.ResidueField O)) (i : O →+* AlgebraicClosure ℚ),
      Function.Injective i ∧ (∀ r : O, i r ∈ B) ∧
      (∀ σ ∈ B.inertiaSubgroupIn ℚ, ∀ r : O, σ (i r) = i r) ∧
      (∀ n : ℕ, ¬ ℓ ∣ n → IsUnit ((n : ℕ) : O)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_dvr_henselian_inertiaField_of_liesOverPrime.solution
