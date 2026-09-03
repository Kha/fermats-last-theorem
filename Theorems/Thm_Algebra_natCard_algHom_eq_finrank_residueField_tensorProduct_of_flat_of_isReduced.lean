import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_Algebra_natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem Algebra.natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] [IsAlgClosed K]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Flat R B]
    [IsReduced (TensorProduct R K B)] :
    Nat.card (B →ₐ[R] K) = Module.finrank (IsLocalRing.ResidueField R) (TensorProduct R (IsLocalRing.ResidueField R) B) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced.solution
