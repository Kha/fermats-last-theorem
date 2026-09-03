import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_NeronModelInfra_NeronModelPropertyBundle_exists_section_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem NeronModelInfra.NeronModelPropertyBundle.exists_section_comp_eq
    {R K : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (h : NeronModelPropertyBundle R K f)
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ s : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s.1 = x := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_NeronModelPropertyBundle_exists_section_comp_eq.solution
