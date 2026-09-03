import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo.GoodReductionJacobian"

universe u

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp RelativeGroupLaw RelativeGroupLaw.fibreStr RelativeGroupLaw.fibrePointToBase_coe RelativeGroupLaw.fibrePointOfBase_coe RelativeGroupLaw.idPoint"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "baseResidueField fibreStr fibrePointToBase fibrePointOfBase fibrePointToBase_coe fibrePointOfBase_coe fibrePointToBase_ofBase fibre fibre_mul nsmul nsmul_succ nsmul_natural idPoint schemeNsmul schemeNsmul_over"
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem fibre_nsmul (G : RelativeGroupLaw R f) (s : (Spec (CommRingCat.of R) : Scheme.{u}))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) (n : ℕ)
    (x : SchemeHomOver t' (fibreStr f s)) :
    (G.fibre s).nsmul t' n x = fibrePointOfBase s (G.nsmul _ n (fibrePointToBase s x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nsmul_succ, ih, fibre_mul, fibrePointToBase_ofBase, nsmul_succ]

theorem nsmul_coe_eq_comp_schemeNsmul' (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hid : schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x := Subtype.ext (Category.comp_id x.1)
  have h : schemeHomOverComp x.1 x.2 (G.nsmul f n idPoint)
      = G.nsmul t n (schemeHomOverComp x.1 x.2 idPoint) :=
    G.nsmul_natural f t x.1 x.2 n idPoint
  rw [hid] at h
  exact (congrArg Subtype.val h).symm

end GoodReductionJacobian.RelativeGroupLaw

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (s : (Spec (CommRingCat.of R) : Scheme.{u})) (n : ℕ) :
    (G.fibre s).schemeNsmul n = schemeFibreEndo f (G.schemeNsmul n) (G.schemeNsmul_over n) s := by
  apply pullback.hom_ext
  · rw [schemeFibreEndo_fst]
    show ((G.fibre s).nsmul (RelativeGroupLaw.fibreStr f s) n RelativeGroupLaw.idPoint).1 ≫ _ = _
    rw [RelativeGroupLaw.fibre_nsmul, RelativeGroupLaw.fibrePointOfBase_coe, pullback.lift_fst,
      RelativeGroupLaw.nsmul_coe_eq_comp_schemeNsmul', RelativeGroupLaw.fibrePointToBase_coe]
    simp only [Category.id_comp]
  · rw [schemeFibreEndo_snd]
    exact (G.fibre s).schemeNsmul_over n
