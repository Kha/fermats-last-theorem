import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (k : Type u) [CommRing k] [Algebra R k]
    [IsDomain (k ⊗[R] (𝒱.cover c).A0)] [IsDomain (k ⊗[R] (𝒱.cover c).A1)]
    [Nontrivial (k ⊗[R] (𝒱.cover c).A01)] :
    IsIntegral (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R k)) ∧
      Nonempty (𝒱.pullback c k).U0 ∧ Nonempty (𝒱.pullback c k).U1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct.solution
