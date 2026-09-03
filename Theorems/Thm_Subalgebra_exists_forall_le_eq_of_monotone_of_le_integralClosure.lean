import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_exists_forall_le_eq_of_monotone_of_le_integralClosure

set_option autoImplicit false

theorem Subalgebra.exists_forall_le_eq_of_monotone_of_le_integralClosure
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [CommRing L] [IsReduced L] [Algebra K L] [Module.Finite K L]
    [Algebra R L] [IsScalarTower R K L]
    (D : ℕ → Subalgebra R L) (hmono : Monotone D) (hint : ∀ i, D i ≤ integralClosure R L) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → D i = D i₀ := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_exists_forall_le_eq_of_monotone_of_le_integralClosure.solution
