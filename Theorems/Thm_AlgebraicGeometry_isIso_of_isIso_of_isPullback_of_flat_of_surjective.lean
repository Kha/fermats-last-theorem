import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isIso_of_isPullback_of_flat_of_surjective
    {S S' A B A' B' : Scheme.{0}} (b : S' ⟶ S) [Flat b] [Surjective b] [QuasiCompact b]
    (pA : A ⟶ S) (pB : B ⟶ S) (φ : A ⟶ B) (hφ : φ ≫ pB = pA)
    (pA' : A' ⟶ S') (pB' : B' ⟶ S') (φ' : A' ⟶ B') (hφ' : φ' ≫ pB' = pA')
    (gA : A' ⟶ A) (gB : B' ⟶ B) (sqA : IsPullback gA pA' pA b) (sqB : IsPullback gB pB' pB b)
    (comm : φ' ≫ gB = gA ≫ φ) (hiso : IsIso φ') :
    IsIso φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective.solution
