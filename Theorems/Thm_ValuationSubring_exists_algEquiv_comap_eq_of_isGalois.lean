import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_algEquiv_comap_eq_of_isGalois

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_algEquiv_comap_eq_of_isGalois
    {E K : Type*} [Field E] [Field K] [Algebra E K] [FiniteDimensional E K] [IsGalois E K]
    (V : ValuationSubring E) [IsDiscreteValuationRing ↥V]
    (B B' : ValuationSubring K)
    (hB : ∀ x : E, algebraMap E K x ∈ B ↔ x ∈ V) (hB' : ∀ x : E, algebraMap E K x ∈ B' ↔ x ∈ V) :
    ∃ σ : K ≃ₐ[E] K, B' = B.comap σ.toAlgHom.toRingHom := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_algEquiv_comap_eq_of_isGalois.solution
