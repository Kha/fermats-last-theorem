import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_finrank_sections_eq_of_iso_pullback_translate

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.finrank_sections_eq_of_iso_pullback_translate
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓜 : A.Modules) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (𝓝 : A.Modules) (e : 𝓝 ≅ (Scheme.Modules.pullback (L.translate x)).obj 𝓜) :
    letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module k Γ(𝓜, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
    letI : Module k Γ(𝓝, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
    Module.finrank k Γ(𝓝, ⊤) = Module.finrank k Γ(𝓜, ⊤) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_finrank_sections_eq_of_iso_pullback_translate.solution
