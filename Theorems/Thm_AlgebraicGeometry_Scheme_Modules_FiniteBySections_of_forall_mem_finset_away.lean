import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_forall_mem_finset_away

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_forall_mem_finset_away
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (M : X.Modules) (hinv : Scheme.Modules.IsInvertible M)
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ g ∈ s, Scheme.Modules.FiniteBySections
        ((Scheme.Modules.pullback (Limits.pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))))).obj M)
        (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))))) :
    Scheme.Modules.FiniteBySections M f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_forall_mem_finset_away.solution
