import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.AffSES.injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
    {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)
    (h₃ : ∀ i : ℕ, Subsingleton (F₃.HSucc K i))
    (hsurj : Function.Surjective (S.proj.H0Map K)) :
    ∀ i : ℕ, Function.Injective (S.inc.HSuccMap K i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map.solution
