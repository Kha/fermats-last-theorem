import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorUnit_app_eq_smul

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite"

theorem solution
    {X : Scheme.{u}} (r : Γ(X, ⊤)) :
    ∃ t : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules,
      (∀ (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)),
        t.app U m = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r • m) ∧
      t.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = r • Scheme.Modules.toUnitSection ⊤ 1 := by
  let s : SheafOfModules.sections (R := X.ringCatSheaf) (𝟙_ X.Modules) :=
    PresheafOfModules.sectionsMk
      (fun U => Scheme.Modules.toUnitSection U.unop (X.presheaf.map (homOfLE le_top).op r))
      (by
        intro U V i
        change Scheme.Modules.toUnitSection V.unop
            (X.presheaf.map i (X.presheaf.map (homOfLE le_top).op r)) = _
        rw [← CommRingCat.comp_apply, ← Functor.map_comp]
        rfl)
  let t : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules := (SheafOfModules.unitHomEquiv (𝟙_ X.Modules)).symm s
  have h1 : ∀ U : X.Opens, t.app U (Scheme.Modules.toUnitSection U 1)
      = Scheme.Modules.toUnitSection U (X.presheaf.map (homOfLE le_top).op r) := by
    intro U
    have := SheafOfModules.unitHomEquiv_apply_coe (𝟙_ X.Modules) t (op U)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have key : ∀ (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)),
      t.app U m = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r • m := by
    intro U m
    have hm : m = Scheme.Modules.ofUnitSection U m • Scheme.Modules.toUnitSection U 1 := by
      apply Scheme.Modules.ofUnitSection_injective
      rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]
    rw [hm, Scheme.Modules.Hom.app_smul, h1, smul_smul]
    apply Scheme.Modules.ofUnitSection_injective
    rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_smul,
      Scheme.Modules.ofUnitSection_toUnitSection, Scheme.Modules.ofUnitSection_toUnitSection,
      mul_one, mul_comm]
  refine ⟨t, key, ?_⟩
  rw [key]
  congr 1
  change (X.presheaf.map (𝟙 (op ⊤))) r = r
  rw [X.presheaf.map_id]
  rfl
