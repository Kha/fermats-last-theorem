import Mathlib
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_stalkQuotient_of_forall_flat_schemeFibreEndo
attribute [-instance] kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.flat_stalkQuotient_of_forall_flat_schemeFibreEndo
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ X) (hcomm : h ≫ f = f) [Smooth f] [IsSeparated f] (x : X)
    (hfib : ∀ s, Flat (schemeFibreEndo f h hcomm s)) :
    letI := (f.stalkMap (h.base x)).hom.toAlgebra
    letI := (h.stalkMap x).hom.toAlgebra
    letI := ((h.stalkMap x).hom.comp (f.stalkMap (h.base x)).hom).toAlgebra
    haveI : IsScalarTower ((Spec (CommRingCat.of R)).presheaf.stalk (f.base (h.base x)))
        (X.presheaf.stalk (h.base x)) (X.presheaf.stalk x) := .of_algebraMap_eq' rfl
    letI := Ideal.Quotient.algebraQuotientOfLEComap
      (p := (IsLocalRing.maximalIdeal
        ((Spec (CommRingCat.of R)).presheaf.stalk (f.base (h.base x)))).map
        (f.stalkMap (h.base x)).hom)
      (P := (IsLocalRing.maximalIdeal
        ((Spec (CommRingCat.of R)).presheaf.stalk (f.base (h.base x)))).map
        ((h.stalkMap x).hom.comp (f.stalkMap (h.base x)).hom))
      (by rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]; exact le_rfl)
    Module.Flat ((X.presheaf.stalk (h.base x)) ⧸
        (IsLocalRing.maximalIdeal
          ((Spec (CommRingCat.of R)).presheaf.stalk (f.base (h.base x)))).map
          (f.stalkMap (h.base x)).hom)
      ((X.presheaf.stalk x) ⧸
        (IsLocalRing.maximalIdeal
          ((Spec (CommRingCat.of R)).presheaf.stalk (f.base (h.base x)))).map
          ((h.stalkMap x).hom.comp (f.stalkMap (h.base x)).hom)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_stalkQuotient_of_forall_flat_schemeFibreEndo.solution
