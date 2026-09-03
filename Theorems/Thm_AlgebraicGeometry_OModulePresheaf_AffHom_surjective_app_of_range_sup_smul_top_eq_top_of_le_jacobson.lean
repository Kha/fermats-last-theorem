import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_AffHom_surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.AffHom.surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [UniversallyClosed f]
    {F G : OModulePresheaf f} (hF : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (φ : OModulePresheaf.AffHom F G)
    (h : ∀ U : X.affineOpens, LinearMap.range (φ.app U) ⊔ I • (⊤ : Submodule R (G.obj U.1)) = ⊤)
    (U : X.affineOpens) : Function.Surjective (φ.app U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson.solution
