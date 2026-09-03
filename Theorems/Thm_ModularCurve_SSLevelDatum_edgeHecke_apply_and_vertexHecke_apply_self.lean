import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ComponentGroupHecke
import P2M.Util
import P2M.Sol.S_ModularCurve_SSLevelDatum_edgeHecke_apply_and_vertexHecke_apply_self

set_option autoImplicit false

open AlgebraicCurve ModularCurve Classical

theorem ModularCurve.SSLevelDatum.edgeHecke_apply_and_vertexHecke_apply_self
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p] [DecidableEq K]
    {M s : ℕ} [NeZero M] [NeZero s] (X : SSLevelDatum p K M s)
    (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) = p) :
    (∀ y x : ↥(ssPlaces p (M * s) K),
        X.edgeHecke ℓ y x = if frobOnPlacesGeomLevel K (M * s) X.frobData X.kronecker x.1 = y.1 then 1 else 0) ∧
    (∀ y x : ↥(ssPlaces p M K),
        X.vertexHecke ℓ y x = if frobOnPlacesGeomLevel K M X.frobData X.kronecker x.1 = y.1 then 1 else 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SSLevelDatum_edgeHecke_apply_and_vertexHecke_apply_self.solution
