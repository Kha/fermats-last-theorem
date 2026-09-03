import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import P2M.Util
import P2M.Sol.S_NeronModelInfra_TopFormOrder_le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul

set_option autoImplicit false

universe u

open NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
    (R' K' O' O F : Type u)
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    (ϖ : R') (hϖ : IsLocalRing.maximalIdeal R' = Ideal.span {ϖ})
    [CommRing O'] [IsDomain O'] [Algebra R' O']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Algebra O' O] [IsScalarTower R' O' O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra O' F] [IsScalarTower O' O F] [IsFractionRing O' F]
    [Algebra K' F] [Algebra R' F] [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    (d : ℕ) (b' : Module.Basis (Fin d) O' (Ω[O'⁄R'])) (b : Module.Basis (Fin d) O (Ω[O⁄R']))
    (m : ℤ) (u : O'ˣ) (σ : ⋀[F]^d (Ω[F⁄K']))
    (hσ : letI := moduleAlong O' F (⋀[F]^d (Ω[F⁄K']))
      σ = (algebraMap O' F (u : O') * algebraMap O' F (algebraMap R' O' ϖ) ^ m) •
        topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b')) :
    m ≤ ord R' K' O d F σ ∧
    (ord R' K' O d F σ = m ↔ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O)) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul.solution
