import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import P2M.Util
import P2M.Sol.S_NeronModelInfra_TopFormOrder_eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le

set_option autoImplicit false

universe u

open TensorProduct NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le

    (R K R' K' : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    (hRR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    [Field K'] [Algebra R' K'] [IsFractionRing R' K'] [Algebra K K'] [Algebra R K']
    [IsScalarTower R K K'] [IsScalarTower R R' K']

    (O₀ F₀ : Type u)
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra R O₀] [IsLocalHom (algebraMap R O₀)]
    (hO₀ : Ideal.map (algebraMap R O₀) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O₀)
    [Field F₀] [Algebra O₀ F₀] [IsFractionRing O₀ F₀] [Algebra K F₀] [Algebra R F₀]
    [IsScalarTower R O₀ F₀] [IsScalarTower R K F₀]
    (d : ℕ) (b₀ : Module.Basis (Fin d) O₀ (Ω[O₀⁄R])) (a : F₀) (ha : a ≠ 0)

    (O₁ O' : Type u)
    [CommRing O₁] [Algebra R O₁]
    [CommRing O'] [IsDomain O'] [Algebra R' O'] [Algebra O₁ O'] [Algebra R O']
    [IsScalarTower R O₁ O'] [IsScalarTower R R' O']
    (b₁ : Module.Basis (Fin d) O₁ (Ω[O₁⁄R])) (w₁ : O₁ˣ) (m : ℤ)
    (hbc' : Function.Bijective
      ((KaehlerDifferential.map R R' O' O').restrictScalars O' ∘ₗ KaehlerDifferential.mapBaseChange R O₁ O'))

    (O F : Type u)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Algebra R O] [IsScalarTower R R' O]
    [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)] [IsScalarTower R O₀ O]
    [Algebra O' O] [IsScalarTower R' O' O] [Algebra O₁ O] [IsScalarTower O₁ O' O] [IsScalarTower R O₁ O]
    (hbc : Function.Bijective
      ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R O₀ O))
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra O' F] [IsScalarTower O' O F] [IsFractionRing O' F]
    [Algebra K' F] [Algebra R' F] [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    [Algebra K F] [Algebra R F] [IsScalarTower R O F] [IsScalarTower R K F] [IsScalarTower K K' F]
    [Algebra F₀ F] [Algebra O₀ F] [IsScalarTower O₀ O F] [IsScalarTower O₀ F₀ F] [IsScalarTower K F₀ F]
    [Algebra O₁ F] [IsScalarTower O₁ O F] [IsScalarTower R O₁ F]

    (σ : ⋀[F]^d (Ω[F⁄K]))
    (hT : σ = (algebraMap O₁ F (w₁ : O₁) * algebraMap O₁ F (algebraMap R O₁ ϖ) ^ m) •
        topFormMap R K O₁ F d (exteriorPower.ιMulti O₁ d b₁))
    (hX : topFormMap K K' F F d σ =
        topFormMap K K' F₀ F d (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b₀)))
    (hmin : addOrd O₀ F₀ a ≤ m) :
    m = addOrd O₀ F₀ a ∧ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le.solution
