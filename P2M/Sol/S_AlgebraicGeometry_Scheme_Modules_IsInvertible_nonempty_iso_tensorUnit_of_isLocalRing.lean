import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry"
open AlgebraicGeometry.Scheme.Modules

namespace R2P

set_option maxHeartbeats 1600000 in
theorem nonempty_iso_unit_of_isFrameOn_top {X : Scheme.{u}} {N : X.Modules} (s : Γ(N, ⊤))
    (hs : IsFrameOn s ⊤) : Nonempty (N ≅ 𝟙_ X.Modules) := by
  obtain ⟨θ, hθ, -⟩ := IsFrameOn.existsUnique_ihomEval_eq (isFrameOn_unitSection (X := X) (U := ⊤) ⊤) s
  let μ : 𝟙_ X.Modules ⟶ N := ihomGlobalSectionsEquiv (𝟙_ X.Modules) N θ
  have hμ : μ.app ⊤ (unitSection ⊤) = s := by
    rw [ihomGlobalSectionsEquiv_app_apply]
    have e : ((ihom (𝟙_ X.Modules)).obj N).presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op θ = θ := by
      rw [Subsingleton.elim (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) (𝟙 _), op_id, CategoryTheory.Functor.map_id]; rfl
    rw [e]; exact hθ
  haveI : IsIso μ := isIso_of_isFrameOn_of_iSup_eq_top μ (fun _ : Unit => (⊤ : X.Opens))
    (by rw [iSup_const]) (fun _ => unitSection ⊤) (fun _ => s)
    (fun _ => isFrameOn_unitSection (X := X) (U := ⊤) ⊤) (fun _ => hs) (fun _ => hμ)
  exact ⟨(asIso μ).symm⟩

end R2P

set_option maxHeartbeats 1600000 in

theorem solution
    {A : Type u} [CommRing A] [IsLocalRing A] {N : (Spec (CommRingCat.of A)).Modules}
    (hN : Scheme.Modules.IsInvertible N) : Nonempty (N ≅ 𝟙_ (Spec (CommRingCat.of A)).Modules) := by
  obtain ⟨U, s, hx, hs⟩ := hN.exists_isFrameOn (IsLocalRing.closedPoint A)
  have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hx
  subst hU
  exact R2P.nonempty_iso_unit_of_isFrameOn_top s hs
