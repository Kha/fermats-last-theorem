import Mathlib
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelN_isZeroAtImInfty_slash_of_mem_regularDifferentials

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.LevelN.isZeroAtImInfty_slash_of_mem_regularDifferentials (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K]
    (ω : KaehlerDifferential ℂ K) (hω : ω ∈ AlgebraicCurve.regularDifferentials ℂ K)
    (F : UpperHalfPlane → ℂ)
    (hF : ∀ (a b c e : UpperHalfPlane → ℂ) (ha : a ∈ ModularCurve.LevelN.ring N)
      (hb : b ∈ ModularCurve.LevelN.ring N) (hc : c ∈ ModularCurve.LevelN.ring N)
      (he : e ∈ ModularCurve.LevelN.ring N), b ≠ 0 → e ≠ 0 →
      ω = (algebraMap (ModularCurve.LevelN.ring N) K ⟨a, ha⟩ /
            algebraMap (ModularCurve.LevelN.ring N) K ⟨b, hb⟩) •
          KaehlerDifferential.D ℂ K (algebraMap (ModularCurve.LevelN.ring N) K ⟨c, hc⟩ /
            algebraMap (ModularCurve.LevelN.ring N) K ⟨e, he⟩) →
      ∀ τ : UpperHalfPlane, F τ * b τ * e τ ^ 2 =
        a τ * (e τ * deriv (c ∘ UpperHalfPlane.ofComplex) τ -
          c τ * deriv (e ∘ UpperHalfPlane.ofComplex) τ))
    (δ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty (F ∣[(2 : ℤ)] δ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelN_isZeroAtImInfty_slash_of_mem_regularDifferentials.solution
