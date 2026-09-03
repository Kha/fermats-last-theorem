import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))
    (m : ℕ) {i : Fin (N + 1)} {W : X.Opens} (hW : W ≤ ProjSpace.pullbackChart φ i) :
    ∃ e : ProjSpace.twistObj π φ m W ≃ₗ[Γ(X, W)] Γ(X, W),
      (∀ g : ProjSpace.twistObj π φ m W,
        ProjSpace.restrictFun (inf_le_left : W ⊓ ProjSpace.pullbackChart φ i ≤ W) (e g) = g.val i) ∧
      (∀ (a : Γ(X, W)) (j : Fin (N + 1)),
        (e.symm a).val j =
          ProjSpace.restrictFun (inf_le_right : W ⊓ ProjSpace.pullbackChart φ j ≤ ProjSpace.pullbackChart φ j)
              (ProjSpace.frameUnit φ j i) ^ m *
            ProjSpace.restrictFun (inf_le_left : W ⊓ ProjSpace.pullbackChart φ j ≤ W) a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.solution
