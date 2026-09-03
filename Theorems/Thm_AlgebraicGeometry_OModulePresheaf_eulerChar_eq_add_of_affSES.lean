import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.eulerChar_eq_add_of_affSES
    {k : Type u} [Field k] {V : Scheme.{u}} {π : V ⟶ Spec (.of k)} [IsSeparated π]
    {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)
    (h₁ : F₁.CechFinite K) (h₂ : F₂.CechFinite K) (h₃ : F₃.CechFinite K) :
    F₂.eulerChar K = F₁.eulerChar K + F₃.eulerChar K := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.solution
