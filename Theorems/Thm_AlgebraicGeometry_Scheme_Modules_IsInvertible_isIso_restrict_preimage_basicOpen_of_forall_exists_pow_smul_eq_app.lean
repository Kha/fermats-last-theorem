import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_restrict_preimage_basicOpen_of_forall_exists_pow_smul_eq_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_restrict_preimage_basicOpen_of_forall_exists_pow_smul_eq_app
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact h] [QuasiSeparated h]
    (hΓ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop).hom)
    (P : Y.Modules) (hP : Scheme.Modules.IsInvertible P)
    (hloc : ∀ y : ↥(Spec (CommRingCat.of R)), ∃ U : (Spec (CommRingCat.of R)).Opens, y ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (h ⁻¹ᵁ U).ι).obj P ≅ SheafOfModules.unit (↑(h ⁻¹ᵁ U) : Scheme.{u}).ringCatSheaf))
    (θ : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ P) (u : R)
    (hgen : ∀ m : Γ(P, ⊤), ∃ (n : ℕ) (x : Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤)),
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop).hom (u ^ n)) • m = Scheme.Modules.Hom.app θ ⊤ x) :
    IsIso ((Scheme.Modules.pullback (h ⁻¹ᵁ (PrimeSpectrum.basicOpen u)).ι).map θ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_restrict_preimage_basicOpen_of_forall_exists_pow_smul_eq_app.solution
