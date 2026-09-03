import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_le_mem_nonempty_pullback_iso_of_nonempty_iso_unit_of_isDiscreteValuationRing_stalk
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_basicOpen_le_mem_nonempty_pullback_iso_of_isDiscreteValuationRing_stalk

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem solution
    {X : Scheme.{0}} (t : Γ(X, ⊤)) (ξ : X)
    [IsDomain (X.presheaf.stalk ξ)] [IsDiscreteValuationRing (X.presheaf.stalk ξ)]
    (hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) = Ideal.span {X.presheaf.Γgerm ξ t})
    (L L' : X.Modules) (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (h : Nonempty ((Scheme.Modules.pullback (X.basicOpen t).ι).obj L ≅ (Scheme.Modules.pullback (X.basicOpen t).ι).obj L')) :
    ∃ V : X.Opens, X.basicOpen t ≤ V ∧ ξ ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj L ≅ (Scheme.Modules.pullback V.ι).obj L') := by

  obtain ⟨W₁, hξ₁, ⟨e₁⟩⟩ := hL.exists_trivialization ξ
  obtain ⟨W₂, hξ₂, ⟨e₂⟩⟩ := hL'.exists_trivialization ξ
  let W : X.Opens := W₁ ⊓ W₂

  have restr : ∀ (N : X.Modules) (W₀ : X.Opens) (hle : W ≤ W₀),
      ((Scheme.Modules.pullback W₀.ι).obj N ≅ SheafOfModules.unit W₀.toScheme.ringCatSheaf) →
      Nonempty ((Scheme.Modules.pullback W.ι).obj N ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) := by
    intro N W₀ hle e
    exact ⟨((Scheme.Modules.pullbackCongr (X.homOfLE_ι hle)).app N).symm ≪≫
      ((Scheme.Modules.pullbackComp (X.homOfLE hle) W₀.ι).app N).symm ≪≫
      (Scheme.Modules.pullback (X.homOfLE hle)).mapIso e ≪≫
      Scheme.Modules.pullbackUnitIso (X.homOfLE hle)⟩
  exact AlgebraicGeometry.Scheme.Modules.exists_basicOpen_le_mem_nonempty_pullback_iso_of_nonempty_iso_unit_of_isDiscreteValuationRing_stalk
    t ξ hmax L L' W ⟨hξ₁, hξ₂⟩ (restr L W₁ inf_le_left e₁) (restr L' W₂ inf_le_right e₂) h
