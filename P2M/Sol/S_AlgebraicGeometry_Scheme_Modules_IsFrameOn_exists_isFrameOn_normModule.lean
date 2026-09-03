import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_basis_smul_pushforward
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isFrameOn_sheafificationAdjunction_unit_iotaMulti
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_normModule

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite"

theorem solution
    {X Y : Scheme.{u}} (π : X ⟶ Y) (d : ℕ) {L : X.Modules} {V : Y.Opens}
    (e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V))
    (he : ∀ (W : Y.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin d) Γ(Y, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).presheaf.map (homOfLE hW).op (e i))
    {s : Γ(L, π ⁻¹ᵁ V)} (hs : Scheme.Modules.IsFrameOn s (π ⁻¹ᵁ V)) :
    ∃ q : Γ(Scheme.Modules.dual (Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules))), V),
      Scheme.Modules.IsFrameOn q V ∧
      Scheme.Modules.ihomEval (Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)))
          (𝟙_ Y.Modules) V
        (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
            ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).val)).app
          (op V)
          (show ((Scheme.Modules.presheafExteriorPower Y d).obj
              ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).val).obj (op V) from exteriorPower.ιMulti Γ(Y, V) d e))
        q = Scheme.Modules.unitSection V ∧
      Scheme.Modules.IsFrameOn (M := Scheme.Modules.normModule π d L)
        (Scheme.Modules.tensorSections
          (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
              ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj L).val)).app (op V)
            (show ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj L).val).obj (op V)
              from exteriorPower.ιMulti Γ(Y, V) d
                (fun i => (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from e i) • s))))
          q)
        V := by

  have hE := Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti
    (M := (Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)) e he

  obtain ⟨q, hq, hq1⟩ := hE.exists_isFrameOn_dual (le_refl V)

  have hES := Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti
    (M := (Scheme.Modules.pushforward π).obj L)
    (fun i => (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from e i) • s))
    (Scheme.Modules.IsFrameOn.exists_basis_smul_pushforward π e he hs)
  refine ⟨q, hq, ?_, ?_⟩
  ·
    have hid : ∀ (M : Y.Modules) (x : Γ(M, V)), M.presheaf.map (homOfLE (le_refl V)).op x = x := fun M x => by
      rw [show (homOfLE (le_refl V)).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]; rfl
    rw [hid] at hq1
    exact hq1
  · exact hES.tensorSections hq
