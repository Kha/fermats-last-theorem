import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_locallyQuasiFinite_of_field
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_forall_flat_fibre_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_forall_surjective_fibre_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_flat_surjective_locallyQuasiFinite_of_forall_locallyQuasiFinite_fibre_schemeNsmul
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_flat_surjective_locallyQuasiFinite_of_forall_locallyQuasiFinite_fibre_schemeNsmul
    {R : Type u} [CommRing R] {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)} [Smooth g]
    (L : RelativeGroupLaw R g) (hc : L.IsCommutative)
    (hconn : ∀ s : Spec (CommRingCat.of R), _root_.IsPreconnected (g.base ⁻¹' {s}))
    (hfib : ∀ (s : Spec (CommRingCat.of R)) (n : ℕ), 0 < n → ¬ IsUnit ((n : GoodReductionJacobian.RelativeGroupLaw.baseResidueField s)) →
      LocallyQuasiFinite ((L.fibre s).schemeNsmul n)) :
    (∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n)) ∧ (∀ n : ℕ, 0 < n → Surjective (L.schemeNsmul n)) ∧
      (∀ n : ℕ, 0 < n → LocallyQuasiFinite (L.schemeNsmul n)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_flat_surjective_locallyQuasiFinite_of_forall_locallyQuasiFinite_fibre_schemeNsmul.solution
