import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_algHom_apply_algebraMap_eq_pow_card_of_constantsAreBase

set_option autoImplicit false

theorem AlgebraicCurve.exists_algHom_apply_algebraMap_eq_pow_card_of_constantsAreBase
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [Field F₀] [Field F]
    [Algebra k K] [Algebra k F₀] [Algebra F₀ F] [Algebra K F] [Algebra k F]
    [IsScalarTower k K F] [IsScalarTower k F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [Algebra.EssFiniteType k F₀] [Algebra.IsAlgebraic k K]
    (hC : AlgebraicCurve.ConstantsAreBase k F₀)
    (hgen : Algebra.adjoin F₀ (Set.range (algebraMap K F)) = ⊤) :
    ∃ φ : F →ₐ[K] F, ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_algHom_apply_algebraMap_eq_pow_card_of_constantsAreBase.solution
