import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isAffineOpen_of_dense_of_ringKrullDim_le_one

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isAffineOpen_of_dense_of_ringKrullDim_le_one
    {B : Type u} [CommRing B] [IsNoetherianRing B] (hB : ringKrullDim B ≤ 1)
    (U : (Spec (CommRingCat.of B)).Opens) (hU : Dense (U : Set (Spec (CommRingCat.of B)))) :
    IsAffineOpen U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isAffineOpen_of_dense_of_ringKrullDim_le_one.solution
