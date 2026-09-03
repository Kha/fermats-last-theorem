import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_locallyTrivial_opensRange_nonempty_pullback_iso

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_locallyTrivial_opensRange_nonempty_pullback_iso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : U.Modules} (hM : Scheme.Modules.IsInvertible M) :
    ∃ 𝓛 : X.Modules,
      (∀ x ∈ Scheme.Hom.opensRange j, ∃ U : X.Opens, x ∈ U ∧ U ≤ Scheme.Hom.opensRange j ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛 ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)) ∧
      Nonempty ((Scheme.Modules.pullback j).obj 𝓛 ≅ M) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_locallyTrivial_opensRange_nonempty_pullback_iso.solution
