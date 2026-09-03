import Mathlib
import P2M.Util
import P2M.Sol.S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra

set_option autoImplicit false

universe u v w

theorem IsNoetherianRing.of_ringKrullDim_le_one_of_finiteDimensional_subalgebra
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type w) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] [FiniteDimensional K L]
    (B : Subalgebra R L) :
    IsNoetherianRing ↥B ∧ ringKrullDim ↥B ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra.solution
