import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import P2M.Util
import P2M.Sol.S_NeronModelInfra_TopFormOrder_span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away

set_option autoImplicit false

universe u

open NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away
    (R K B B' : Type u) [CommRing R] [CommRing K] [Algebra R K] (ϖ : R) [IsLocalization.Away ϖ K]
    [CommRing B] [Algebra R B] [CommRing B'] [Algebra B B'] [Algebra K B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R K B'] [IsLocalization.Away (algebraMap R B ϖ) B']
    (d : ℕ) (β : Module.Basis (Fin d) B (Ω[B⁄R])) :
    letI := moduleAlong B B' (⋀[B']^d (Ω[B'⁄K]))
    Submodule.span B' {topFormMap R K B B' d (exteriorPower.ιMulti B d β)} = ⊤ ∧
      ∀ σ : ⋀[B']^d (Ω[B'⁄K]), Submodule.span B' {σ} = ⊤ →
        ∃ u : B'ˣ, σ = (u : B') • topFormMap R K B B' d (exteriorPower.ιMulti B d β) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away.solution
