import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_modelFamily_finite_catchesIndexOnePoints_of_isProper
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {AK : Scheme.{u}} (gK : AK ⟶ Spec (CommRingCat.of K)) [IsProper gK] :
    ∃ M : ModelFamily R K gK, Finite M.ι ∧
      (∀ i, IsAffine (M.X i) ∧ IsSeparated (M.str i) ∧ Flat (M.str i) ∧
        LocallyOfFiniteType (M.str i) ∧ QuasiCompact (M.str i)) ∧
      M.CatchesIndexOnePoints := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper.solution
