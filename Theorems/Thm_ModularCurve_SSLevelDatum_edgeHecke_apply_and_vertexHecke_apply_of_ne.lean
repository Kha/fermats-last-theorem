import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ComponentGroupHecke
import P2M.Util
import P2M.Sol.S_ModularCurve_SSLevelDatum_edgeHecke_apply_and_vertexHecke_apply_of_ne

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.SSLevelDatum.edgeHecke_apply_and_vertexHecke_apply_of_ne
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p] [DecidableEq K]
    {M s : ℕ} [NeZero M] [NeZero s] (X : SSLevelDatum p K M s)
    (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ p) [NeZero (ℓ : ℕ)] :
    (∀ [HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) ℓ)] (y x : ↥(ssPlaces p (M * s) K)),
        X.edgeHecke ℓ y x =
          Divisor.correspondence (heckeBetaC K (M * s) ℓ) (heckeAlphaC K (M * s) ℓ)
            (X.legsIntegral (M * s) ℓ).2 (X.legsIntegral (M * s) ℓ).1 (Finsupp.single x.1 1) y.1) ∧
    (∀ [HasPrincipalDivisors K ↥(charLDegeneracyRoof K M ℓ)] (y x : ↥(ssPlaces p M K)),
        X.vertexHecke ℓ y x =
          Divisor.correspondence (heckeBetaC K M ℓ) (heckeAlphaC K M ℓ)
            (X.legsIntegral M ℓ).2 (X.legsIntegral M ℓ).1 (Finsupp.single x.1 1) y.1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SSLevelDatum_edgeHecke_apply_and_vertexHecke_apply_of_ne.solution
