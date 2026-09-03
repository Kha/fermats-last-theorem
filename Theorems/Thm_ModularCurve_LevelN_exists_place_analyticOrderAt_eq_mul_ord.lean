import Mathlib
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelN_exists_place_analyticOrderAt_eq_mul_ord

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.LevelN.exists_place_analyticOrderAt_eq_mul_ord (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] (τ₀ : UpperHalfPlane) :
    ∃ (W : AlgebraicCurve.Place ℂ K) (e : ℕ), 0 < e ∧
      ∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N), F ≠ 0 →
        analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (τ₀ : ℂ) ≠ ⊤ ∧
        ((analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (τ₀ : ℂ)).toNat : ℤ) =
          e * W.ord (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelN_exists_place_analyticOrderAt_eq_mul_ord.solution
