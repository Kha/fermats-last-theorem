import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import P2M.Util
import P2M.Sol.S_NeronModelInfra_TopFormOrder_topFormMap_ne_zero_of_bijective_smul_of_isLocalization

set_option autoImplicit false

universe u

open NeronModelInfra

theorem NeronModelInfra.TopFormOrder.topFormMap_ne_zero_of_bijective_smul_of_isLocalization
    (K A F : Type u) [Field K] [CommRing A] [Algebra K A] [Field F] [Algebra A F] [Algebra K F]
    [IsScalarTower K A F] (M : Submonoid A) [IsLocalization M F]
    (d : ℕ) (b : Module.Basis (Fin d) A (Ω[A⁄K]))
    (ω : ⋀[A]^d (Ω[A⁄K])) (hω : Function.Bijective fun g : A => g • ω) :
    TopFormOrder.topFormMap K K A F d ω ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_topFormMap_ne_zero_of_bijective_smul_of_isLocalization.solution
