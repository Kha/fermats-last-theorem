import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ramificationIndex_mul_inertiaDeg_mul_natCard_stabilizer_eq_natCard_stabilizer

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ramificationIndex_mul_inertiaDeg_mul_natCard_stabilizer_eq_natCard_stabilizer
    {k F F' M : Type*} [Field k] [Field F] [Field F'] [Field M]
    [Algebra k F] [Algebra k F'] [Algebra k M] [Algebra F F'] [Algebra F M] [Algebra F' M]
    [IsScalarTower k F F'] [IsScalarTower k F M] [IsScalarTower k F' M] [IsScalarTower F F' M]
    [FiniteDimensional F F'] [FiniteDimensional F' M] [FiniteDimensional F M] [IsGalois F M]
    (c : Place k M) :
    (c.restrict F').ramificationIndex F * (c.restrict F').inertiaDeg F *
        Nat.card {σ : M ≃ₐ[F'] M // SemilinearAut.ofAlgAut (σ.restrictScalars k) • c = c} =
      Nat.card {σ : M ≃ₐ[F] M // SemilinearAut.ofAlgAut (σ.restrictScalars k) • c = c} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ramificationIndex_mul_inertiaDeg_mul_natCard_stabilizer_eq_natCard_stabilizer.solution
