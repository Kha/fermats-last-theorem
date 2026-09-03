import Mathlib
import Theorems.Thm_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq
import P2M.Util
namespace P2MW.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R') (_ : IsNoetherianRing R'),
      Nonempty ((R' ⊗[R] B) ≃ₐ[R'] (Fin (Module.finrank R B) → R')) := by
  haveI : Module.Free R B := Module.free_of_flat_of_isLocalRing
  obtain ⟨R', _, _, _, _, _, ⟨e⟩⟩ :=
    Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq R B
      (Module.finrank R B) (fun p => by rw [Module.rankAtStalk_eq_finrank_of_free]; rfl)
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.FiniteType.isNoetherianRing R R', ⟨e⟩⟩
