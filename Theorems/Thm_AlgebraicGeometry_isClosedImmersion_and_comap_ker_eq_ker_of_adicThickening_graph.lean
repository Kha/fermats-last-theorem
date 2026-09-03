import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~isPullback_adicThickening_pullback"

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph
    {R : Type u} [CommRing R] (I : Ideal R) {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated g]
    (φ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening g I n)
    (hφ : ∀ n : ℕ, φ n ≫ adicThickeningToBase g I n = adicThickeningToBase f I n)
    (hφt : ∀ n : ℕ, adicThickeningTransition f I n ≫ φ (n + 1) = φ n ≫ adicThickeningTransition g I n)
    (γ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening (pullback.fst f g ≫ f) I n)
    (hγ₁ : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.fst f g = adicThickeningι f I n)
    (hγ₂ : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.snd f g = φ n ≫ adicThickeningι g I n) :
    ∀ n : ℕ, IsClosedImmersion (γ n) ∧
      ((γ (n + 1)).ker).comap (adicThickeningTransition (pullback.fst f g ≫ f) I n) = (γ n).ker := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isClosedImmersion_and_comap_ker_eq_ker_of_adicThickening_graph.solution
