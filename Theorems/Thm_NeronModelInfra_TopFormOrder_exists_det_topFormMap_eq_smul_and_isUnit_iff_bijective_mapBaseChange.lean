import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import P2M.Util
import P2M.Sol.S_NeronModelInfra_TopFormOrder_exists_det_topFormMap_eq_smul_and_isUnit_iff_bijective_mapBaseChange

set_option autoImplicit false

universe u

open TensorProduct NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.exists_det_topFormMap_eq_smul_and_isUnit_iff_bijective_mapBaseChange
    (R' K' O' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O'] [Algebra R' O'] [CommRing O] [Algebra R' O] [Algebra O' O] [IsScalarTower R' O' O]
    [CommRing F] [Algebra O F] [Algebra O' F] [IsScalarTower O' O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    (d : ℕ) (b' : Module.Basis (Fin d) O' (Ω[O'⁄R'])) (b : Module.Basis (Fin d) O (Ω[O⁄R'])) :
    ∃ h : O,
      (letI := moduleAlong O' F (⋀[F]^d (Ω[F⁄K']))
       letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
       topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b') =
         algebraMap O F h • topFormMap R' K' O F d (exteriorPower.ιMulti O d b)) ∧
      (IsUnit h ↔ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O)) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_exists_det_topFormMap_eq_smul_and_isUnit_iff_bijective_mapBaseChange.solution
