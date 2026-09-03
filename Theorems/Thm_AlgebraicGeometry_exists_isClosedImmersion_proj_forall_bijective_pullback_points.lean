import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isClosedImmersion_proj_forall_bijective_pullback_points

set_option autoImplicit false
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion"
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_isClosedImmersion_proj_forall_bijective_pullback_points
    (Hilb : Scheme.{0}) (p : Hilb ⟶ Spec (CommRingCat.of ℤ)) (N' : ℕ)
    (ιH : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) ℤ))
    (hιH : IsClosedImmersion ιH) (hιHp : ιH ≫ ProjSpace.π ℤ N' = p)
    (B : Type) [CommRing B] (N k : ℕ) :
    ∃ (W₀ : Scheme.{0}) (πW : W₀ ⟶ Spec (CommRingCat.of B)) (M : ℕ)
      (jW : W₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) B))
      (_ : IsClosedImmersion jW) (_ : jW ≫ ProjSpace.π B M = πW)
      (prH : W₀ ⟶ Hilb)
      (prY : Fin k → (W₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B)))
      (hprY : ∀ i, prY i ≫ ProjSpace.π B N = πW),
      ∀ (R : Type) [CommRing R] [Algebra B R],
        Function.Bijective
          (fun s : {s : Spec (CommRingCat.of R) ⟶ W₀ // s ≫ πW = Spec.map (CommRingCat.ofHom (algebraMap B R))} =>
            (⟨(s.1 ≫ prH, fun i => s.1 ≫ prY i), fun i => by
                rw [Category.assoc, hprY i, s.2]⟩ :
              {y : (Spec (CommRingCat.of R) ⟶ Hilb) ×
                  (Fin k → (Spec (CommRingCat.of R) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B))) //
                ∀ i, y.2 i ≫ ProjSpace.π B N = Spec.map (CommRingCat.ofHom (algebraMap B R))})) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_proj_forall_bijective_pullback_points.solution
