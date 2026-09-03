import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isInvertible_zeroSchemeIdeal_and_flat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.isInvertible_zeroSchemeIdeal_and_flat
    {X T : Scheme.{u}} (q : X ⟶ T) [Flat q] [LocallyOfFiniteType q] [IsLocallyNoetherian T]
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T),
      ((Scheme.Modules.zeroSchemeIdeal s).comap (pullback.fst q x)).IsInvertible) :
    (Scheme.Modules.zeroSchemeIdeal s).IsInvertible ∧
      Flat ((Scheme.Modules.zeroSchemeIdeal s).subschemeι ≫ q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isInvertible_zeroSchemeIdeal_and_flat.solution
