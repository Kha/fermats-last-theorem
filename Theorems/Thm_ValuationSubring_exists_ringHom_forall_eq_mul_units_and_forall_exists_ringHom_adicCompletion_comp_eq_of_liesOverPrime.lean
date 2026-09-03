import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ringHom_forall_eq_mul_units_and_forall_exists_ringHom_adicCompletion_comp_eq_of_liesOverPrime

set_option autoImplicit false

theorem ValuationSubring.exists_ringHom_forall_eq_mul_units_and_forall_exists_ringHom_adicCompletion_comp_eq_of_liesOverPrime
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ (S : Type) (_ : CommRing S) (jA : ↥A →+* S),
      (∀ (α β : ↥A) (u : Sˣ), jA α = jA β * (u : S) → ∃ v : (↥A)ˣ, α = β * (v : ↥A)) ∧
      ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (χ : B →+* ↥A), IsLocalHom χ →
        ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal B) B →+* S,
          ψ.comp (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) = jA.comp χ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ringHom_forall_eq_mul_units_and_forall_exists_ringHom_adicCompletion_comp_eq_of_liesOverPrime.solution
