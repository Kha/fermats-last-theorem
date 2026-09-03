import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_moduleInvertible_sections_of_forall_exists_nonempty_pullback_preimage_iso_unit

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.moduleInvertible_sections_of_forall_exists_nonempty_pullback_preimage_iso_unit
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact h] [QuasiSeparated h]
    (hΓ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop).hom)
    (P : Y.Modules) (hP : Scheme.Modules.IsInvertible P)
    (hloc : ∀ y : ↥(Spec (CommRingCat.of R)), ∃ U : (Spec (CommRingCat.of R)).Opens, y ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (h ⁻¹ᵁ U).ι).obj P ≅ SheafOfModules.unit (↑(h ⁻¹ᵁ U) : Scheme.{u}).ringCatSheaf)) :
    letI : Algebra R Γ(Y, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop).hom.toAlgebra
    letI : Module R Γ(P, ⊤) := Module.compHom _ (algebraMap R Γ(Y, ⊤))
    Module.Invertible R Γ(P, ⊤) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_moduleInvertible_sections_of_forall_exists_nonempty_pullback_preimage_iso_unit.solution
