import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj
    (B : Type) [CommRing B] (X : Scheme.{0}) [CompactSpace X] (πX : X ⟶ Spec (CommRingCat.of B))
    (hQP : ∃ (qpm : ℕ) (qpι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpm + 1)) B)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpm = πX)
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (hρ : ∀ γ : Γ, (ρ γ).hom ≫ πX = πX) :
    ∃ (r : ℕ) (U : Fin r → X.Opens) (hinv : ∀ (γ : Γ) (i : Fin r), (ρ γ).hom ⁻¹ᵁ U i = U i)
      (w : ∀ i j : Fin r, Γ(X, U i)),
      (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ ∧
      (∀ i, w i i = 1) ∧
      (∀ i j k : Fin r,
        X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i k) =
          X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i j) *
            X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (w j k)) ∧
      (∀ i j : Fin r, X.basicOpen (w i j) = U i ⊓ U j) ∧
      (∀ (γ : Γ) (i j : Fin r), (ρ γ).hom.appLE (U i) (U i) (le_of_eq (hinv γ i).symm) (w i j) = w i j) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.solution
