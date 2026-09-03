import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_exists_iSup_eq_top_isFrameOn_of_isSectionRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.exists_iSup_eq_top_isFrameOn_of_isSectionRing
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hva : Scheme.Modules.ClosedImmersionBySections L f) :
    ∃ (N : ℕ) (τ : Fin (N + 1) → 𝓡 1) (V : Fin (N + 1) → X.Opens),
      (⨆ i, V i) = ⊤ ∧ ∀ i, AlgebraicGeometry.Scheme.Modules.IsFrameOn (ι 1 (τ i)) (V i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_exists_iSup_eq_top_isFrameOn_of_isSectionRing.solution
