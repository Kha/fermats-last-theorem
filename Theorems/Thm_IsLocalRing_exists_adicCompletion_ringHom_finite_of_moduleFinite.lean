import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_adicCompletion_ringHom_finite_of_moduleFinite

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem IsLocalRing.exists_adicCompletion_ringHom_finite_of_moduleFinite
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R] [IsLocalRing R]
    [IsNoetherianRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S] :
    ∃ φ : AdicCompletion (IsLocalRing.maximalIdeal R) R →+* AdicCompletion (IsLocalRing.maximalIdeal S) S,
      (∀ r : R, φ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
        algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap R S r)) ∧
      φ.Finite ∧
      (Function.Injective (algebraMap R S) → Function.Injective φ) ∧

      ∃ e : TensorProduct R (AdicCompletion (IsLocalRing.maximalIdeal R) R) S ≃+*
          AdicCompletion (IsLocalRing.maximalIdeal S) S,
        (∀ x : AdicCompletion (IsLocalRing.maximalIdeal R) R, e (x ⊗ₜ[R] (1 : S)) = φ x) ∧
        (∀ s : S, e ((1 : AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗ₜ[R] s) =
          algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) s) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_adicCompletion_ringHom_finite_of_moduleFinite.solution
