import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_finite_away_cover_trivial
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_finite_away_cover_trivial
    {S : Type u} [CommRing S] (N : (Spec (CommRingCat.of S)).Modules) (hN : Scheme.Modules.IsInvertible N) :
    ∃ (k : ℕ) (r : Fin k → S), Ideal.span (Set.range r) = ⊤ ∧
      (∀ i, Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))))).obj N ≅
        SheafOfModules.unit (Spec (CommRingCat.of (Localization.Away (r i)))).ringCatSheaf)) ∧
      Module.FaithfullyFlat S (∀ i : Fin k, Localization.Away (r i)) ∧

      Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i : Fin k, Localization.Away (r i)))))).obj N ≅
        SheafOfModules.unit (Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i)))).ringCatSheaf) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_finite_away_cover_trivial.solution
