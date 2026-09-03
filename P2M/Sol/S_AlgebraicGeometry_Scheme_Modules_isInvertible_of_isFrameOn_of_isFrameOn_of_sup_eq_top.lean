import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_of_forall_exists_isFrameOn
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_of_isFrameOn_of_isFrameOn_of_sup_eq_top

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

set_option maxHeartbeats 3200000 in
theorem solution
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens}
    {a : Γ(M, U)} {b : Γ(M, V)}
    (ha : Scheme.Modules.IsFrameOn a U) (hb : Scheme.Modules.IsFrameOn b V) (hUV : U ⊔ V = ⊤) :
    Scheme.Modules.IsInvertible M := by
  refine Scheme.Modules.isInvertible_of_forall_exists_isFrameOn fun x => ?_
  have hx : x ∈ U ⊔ V := by rw [hUV]; trivial
  rcases (TopologicalSpace.Opens.mem_sup.mp hx) with h | h
  · exact ⟨U, a, h, ha⟩
  · exact ⟨V, b, h, hb⟩
