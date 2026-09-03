import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import P2M.Util
import P2M.Sol.S_NeronModelInfra_TopFormOrder_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top

set_option autoImplicit false

open NeronModelInfra TopFormOrder

universe u

theorem NeronModelInfra.TopFormOrder.exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top
    (R K B B' O : Type u) [CommRing R] [CommRing K] [Algebra R K] (ϖ : R) [IsLocalization.Away ϖ K]
    [CommRing B] [Algebra R B] [CommRing B'] [Algebra B B'] [Algebra K B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R K B'] [IsLocalization.Away (algebraMap R B ϖ) B']
    (d : ℕ) (β : Module.Basis (Fin d) B (Ω[B⁄R]))
    (σ : ⋀[B']^d (Ω[B'⁄K])) (hσ : Submodule.span B' {σ} = ⊤)
    [CommRing O] [IsDomain O] [IsNoetherianRing O] [Algebra B O] [Algebra R O] [IsScalarTower R B O]
    (M : Submonoid B) [IsLocalization M O]
    (hϖ0 : algebraMap R O ϖ ≠ 0) (hϖ : (Ideal.span {algebraMap R O ϖ}).IsPrime) :
    ∃ (b' : Module.Basis (Fin d) O (Ω[O⁄R])) (w : Oˣ) (m : ℤ),
      (∀ i, b' i = KaehlerDifferential.map R R B O (β i)) ∧
      ∀ (F : Type u) [Field F] [Algebra O F] [Algebra R F] [Algebra K F] [Algebra B F] [Algebra B' F]
        [IsScalarTower R O F] [IsScalarTower R K F] [IsScalarTower B O F] [IsScalarTower R B F]
        [IsScalarTower B B' F] [IsScalarTower K B' F],
        topFormMap K K B' F d σ =
          (algebraMap O F (w : O) * algebraMap O F (algebraMap R O ϖ) ^ m) •
            topFormMap R K O F d (exteriorPower.ιMulti O d b') := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top.solution
