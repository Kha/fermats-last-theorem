import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Flat_of_comp_of_isAffineHom_of_flat_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Flat.of_comp_of_isAffineHom_of_flat_of_surjective {X Y S : Scheme.{u}}
    (σ : X ⟶ Y) (y : Y ⟶ S) [Flat (σ ≫ y)] [IsAffineHom σ] [Flat σ] [Surjective σ] : Flat y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Flat_of_comp_of_isAffineHom_of_flat_of_surjective.solution
