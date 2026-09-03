import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_isClosedImmersion_of_forall_isPullback_map_of_span_eq_top

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.isClosedImmersion_of_forall_isPullback_map_of_span_eq_top
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    (N : ℕ) {X : Scheme.{u}} (t : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S))
    {X' : Fin k → Scheme.{u}} (t' : ∀ i, X' i ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (B i)))
    (g : ∀ i, X' i ⟶ X) (hsq : ∀ i, IsPullback (g i) (t' i) t (ProjSpace.map S (B i) N))
    (h : ∀ i, IsClosedImmersion (t' i)) :
    IsClosedImmersion t := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_isClosedImmersion_of_forall_isPullback_map_of_span_eq_top.solution
