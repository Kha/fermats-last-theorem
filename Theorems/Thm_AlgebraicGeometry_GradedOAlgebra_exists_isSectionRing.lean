import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.GradedOAlgebra.exists_isSectionRing
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra S R) (𝓡 : ℕ → Submodule S R) (_ : GradedAlgebra 𝓡)
      (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)), AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing.solution
