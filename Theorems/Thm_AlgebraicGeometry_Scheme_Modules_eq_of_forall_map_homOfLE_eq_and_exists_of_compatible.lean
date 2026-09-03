import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_eq_of_forall_map_homOfLE_eq_and_exists_of_compatible

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (V : X.Opens)
    (hUV : ∀ i, U i ≤ V) (hV : V ≤ ⨆ i, U i) :
    (∀ s t : Γ(M, V),
        (∀ i, M.presheaf.map (homOfLE (hUV i)).op s = M.presheaf.map (homOfLE (hUV i)).op t) → s = t) ∧
      (∀ v : ∀ i, Γ(M, U i),
        (∀ i j, M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (v i) =
            M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (v j)) →
          ∃ s : Γ(M, V), ∀ i, M.presheaf.map (homOfLE (hUV i)).op s = v i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_eq_of_forall_map_homOfLE_eq_and_exists_of_compatible.solution
