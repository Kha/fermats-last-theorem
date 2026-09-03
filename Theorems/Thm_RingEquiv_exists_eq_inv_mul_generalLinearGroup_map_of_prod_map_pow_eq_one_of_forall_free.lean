import Mathlib
import P2M.Util
import P2M.Sol.S_RingEquiv_exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free

set_option autoImplicit false

theorem RingEquiv.exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free
    (K L : Type) [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (hσ : 0 < orderOf σ)
    (S : Type) [CommRing S] [Algebra L S] (θ : S ≃+* S)
    (hθ : ∀ l : L, θ (algebraMap L S l) = algebraMap L S (σ l))
    (hθn : θ ^ orderOf σ = 1)
    (m : ℕ)
    (hfree : ∀ (P : Type) [AddCommGroup P] [Module (RingHom.eqLocus θ.toRingHom (RingHom.id S)) P],
      ((Fin (orderOf σ) → P) ≃ₗ[RingHom.eqLocus θ.toRingHom (RingHom.id S)]
          (Fin (m * orderOf σ) → RingHom.eqLocus θ.toRingHom (RingHom.id S))) →
        Module.Free (RingHom.eqLocus θ.toRingHom (RingHom.id S)) P)
    (x : GL (Fin m) S)
    (hx : ((List.range (orderOf σ)).map
      fun k => Matrix.GeneralLinearGroup.map ((θ ^ k : S ≃+* S) : S →+* S) x).prod = 1) :
    ∃ y : GL (Fin m) S, x = y⁻¹ * Matrix.GeneralLinearGroup.map (θ : S →+* S) y := by p2m_exact_reverting @_root_.P2MW.S_RingEquiv_exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free.solution
