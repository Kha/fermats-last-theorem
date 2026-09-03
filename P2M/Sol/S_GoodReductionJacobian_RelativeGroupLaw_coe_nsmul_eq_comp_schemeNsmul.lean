import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    (G.nsmul t n P).1 = P.1 ≫ G.schemeNsmul n := by

  have hP : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := by
    apply Subtype.ext
    rw [schemeHomOverComp_coe]
    exact Category.comp_id _
  have := G.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint
  rw [hP] at this
  rw [← this, schemeHomOverComp_coe]
  rfl
