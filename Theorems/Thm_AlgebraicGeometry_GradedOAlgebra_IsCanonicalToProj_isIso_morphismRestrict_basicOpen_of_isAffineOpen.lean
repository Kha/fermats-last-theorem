import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_isIso_morphismRestrict_basicOpen_of_isAffineOpen

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.isIso_morphismRestrict_basicOpen_of_isAffineOpen
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (m : ℕ) (hm : 0 < m) (τ : 𝓡 m) (haff : IsAffineOpen (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R))) :
    IsIso (θ ∣_ Proj.basicOpen 𝓡 (τ : R)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_isIso_morphismRestrict_basicOpen_of_isAffineOpen.solution
