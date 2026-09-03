import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import P2M.Util
import P2M.Sol.S_NeronModelInfra_TopFormOrder_ord_topFormMap_eq_ord_of_map_maximalIdeal_eq

set_option autoImplicit false

universe u

open TensorProduct NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.ord_topFormMap_eq_ord_of_map_maximalIdeal_eq
    (R R' K K' O₀ O F₀ F : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    (hRR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    [Field K] [Algebra R K] [IsFractionRing R K] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    [Algebra K K'] [Algebra R K'] [IsScalarTower R K K'] [IsScalarTower R R' K']
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra R O₀] [IsLocalHom (algebraMap R O₀)]
    (hO₀ : Ideal.map (algebraMap R O₀) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O₀)
    [Field F₀] [Algebra O₀ F₀] [IsFractionRing O₀ F₀] [Algebra K F₀] [Algebra R F₀]
    [IsScalarTower R O₀ F₀] [IsScalarTower R K F₀]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' K' F]
    [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)] [Algebra R O] [IsScalarTower R O₀ O] [IsScalarTower R R' O]
    [Algebra F₀ F] [Algebra O₀ F] [IsScalarTower O₀ O F] [IsScalarTower O₀ F₀ F]
    [Algebra K F] [IsScalarTower K K' F] [IsScalarTower K F₀ F]
    (d : ℕ) (b : Module.Basis (Fin d) O₀ (Ω[O₀⁄R]))
    (hbc : Function.Bijective
      ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R O₀ O))
    (hρ : (letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
      topFormMap R' K' O F d (exteriorPower.ιMulti O d
        (fun i => KaehlerDifferential.map R R' O O (KaehlerDifferential.map R R O₀ O (b i))))) ≠ 0)
    (a : F₀) (ha : a ≠ 0) :
    letI := moduleAlong O₀ F₀ (⋀[F₀]^d (Ω[F₀⁄K]))
    letI := moduleAlong F₀ F (⋀[F]^d (Ω[F⁄K']))
    ord R' K' O d F (topFormMap K K' F₀ F d (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b))) =
      ord R K O₀ d F₀ (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b)) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_ord_topFormMap_eq_ord_of_map_maximalIdeal_eq.solution
