import Mathlib
import P2M.Util
import P2M.Sol.S_Module_isClosed_setOf_range_le_smul_top

set_option autoImplicit false

theorem Module.isClosed_setOf_range_le_smul_top
    {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q] (f : P →ₗ[R] Q) :
    IsClosed {x : PrimeSpectrum R | LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)} := by p2m_exact_reverting @_root_.P2MW.S_Module_isClosed_setOf_range_le_smul_top.solution
