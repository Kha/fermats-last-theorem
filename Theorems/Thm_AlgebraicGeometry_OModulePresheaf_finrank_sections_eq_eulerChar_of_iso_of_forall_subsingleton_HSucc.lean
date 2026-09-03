import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_finrank_sections_eq_eulerChar_of_iso_of_forall_subsingleton_HSucc

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.finrank_sections_eq_eulerChar_of_iso_of_forall_subsingleton_HSucc
    {R : Type u} [CommRing R] [Nontrivial R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))
    (𝓟 𝓝 : V.Modules) (e : 𝓝 ≅ 𝓟) (𝒦 : V.OrderedAffineCover)
    (hvan : ∀ i : ℕ, Subsingleton ((OModulePresheaf.ofModules π 𝓟).HSucc 𝒦 i)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π 𝓝 ⊤
    ((Module.finrank R Γ(𝓝, ⊤) : ℕ) : ℤ) = (OModulePresheaf.ofModules π 𝓟).eulerChar 𝒦 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_finrank_sections_eq_eulerChar_of_iso_of_forall_subsingleton_HSucc.solution
