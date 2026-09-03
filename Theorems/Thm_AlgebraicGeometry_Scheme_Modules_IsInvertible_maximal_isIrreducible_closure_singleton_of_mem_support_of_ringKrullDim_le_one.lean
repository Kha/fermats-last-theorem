import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_maximal_isIrreducible_closure_singleton_of_mem_support_of_ringKrullDim_le_one

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.maximal_isIrreducible_closure_singleton_of_mem_support_of_ringKrullDim_le_one
    {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) (hs : s ≠ 0) (x : X)
    (hx : x ∈ (Scheme.Modules.zeroSchemeIdeal s).support) (hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    Maximal (fun C' : Set X => IsIrreducible C' ∧ C' ⊆ (Scheme.Modules.zeroSchemeIdeal s).support) (closure {x}) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_maximal_isIrreducible_closure_singleton_of_mem_support_of_ringKrullDim_le_one.solution
