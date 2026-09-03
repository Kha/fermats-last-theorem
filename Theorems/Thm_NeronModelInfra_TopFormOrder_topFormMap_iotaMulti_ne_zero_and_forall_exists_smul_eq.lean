import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import P2M.Util
import P2M.Sol.S_NeronModelInfra_TopFormOrder_topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq

set_option autoImplicit false

universe u

open NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq
    (R K O F : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing O] [IsDomain O] [Algebra R O] [Field F] [Algebra O F] [IsFractionRing O F]
    [Algebra K F] [Algebra R F] [IsScalarTower R O F] [IsScalarTower R K F]
    (d : ℕ) (b : Module.Basis (Fin d) O (Ω[O⁄R])) :
    letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K]))
    topFormMap R K O F d (exteriorPower.ιMulti O d b) ≠ 0 ∧
      ∀ ω : ⋀[F]^d (Ω[F⁄K]), ∃ a : F, ω = a • topFormMap R K O F d (exteriorPower.ιMulti O d b) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq.solution
