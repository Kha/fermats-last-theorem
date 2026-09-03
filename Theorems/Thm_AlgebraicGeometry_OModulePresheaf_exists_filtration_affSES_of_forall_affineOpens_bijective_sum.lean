import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_filtration_affSES_of_forall_affineOpens_bijective_sum

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_filtration_affSES_of_forall_affineOpens_bijective_sum
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (E : OModulePresheaf π) (d : ℕ) (hd : 0 < d) (F : ℕ → OModulePresheaf π)
    (ι : ∀ j : ℕ, OModulePresheaf.Hom (F j) E)
    (h : ∀ U : V.affineOpens, Function.Bijective
      (fun s : (j : Fin d) → (F j).obj U.1 => ∑ j : Fin d, (ι j).app U.1 (s j))) :
    ∃ P : ℕ → OModulePresheaf π,
      P 0 = OModulePresheaf.zero π ∧ P d = E ∧
      ∀ j : ℕ, j < d → Nonempty (OModulePresheaf.AffSES (P j) (P (j + 1)) (F j)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_filtration_affSES_of_forall_affineOpens_bijective_sum.solution
