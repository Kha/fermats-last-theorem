import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_of_forall_isIso_adicThickening_of_isAdicComplete_of_isClosedImmersion_proj

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.isIso_of_forall_isIso_adicThickening_of_isAdicComplete_of_isClosedImmersion_proj
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {Γ X : Scheme.{u}} (γ : Γ ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιΓ : Γ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hιΓ : IsClosedImmersion ιΓ)
    (hιΓγ : ιΓ ≫ ProjSpace.π R N = γ)
    (N' : ℕ) (ιX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)) (hιX : IsClosedImmersion ιX)
    (hιXf : ιX ≫ ProjSpace.π R N' = f)
    (ψ : Γ ⟶ X) (hψ : ψ ≫ f = γ)
    (ψn : ∀ n : ℕ, adicThickening γ I n ⟶ adicThickening f I n)
    (hψn : ∀ n : ℕ, ψn n ≫ adicThickeningι f I n = adicThickeningι γ I n ≫ ψ)
    (hψn' : ∀ n : ℕ, ψn n ≫ adicThickeningToBase f I n = adicThickeningToBase γ I n)
    (hiso : ∀ n : ℕ, IsIso (ψn n)) :
    IsIso ψ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_forall_isIso_adicThickening_of_isAdicComplete_of_isClosedImmersion_proj.solution
