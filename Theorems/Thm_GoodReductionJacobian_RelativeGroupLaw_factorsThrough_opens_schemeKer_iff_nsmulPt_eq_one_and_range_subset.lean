import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_factorsThrough_opens_schemeKer_iff_nsmulPt_eq_one_and_range_subset

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing
open scoped Quaternion TensorProduct NumberField

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.factorsThrough_opens_schemeKer_iff_nsmulPt_eq_one_and_range_subset
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) (Z : Set ↥A)
    (W : (L.schemeKer n).Opens)
    (hW : (W : Set ↥(L.schemeKer n))
      = (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1).base ⁻¹' Z)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    FactorsThrough (W.ι ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) P ↔
      nsmulPt L t n P = L.one t ∧ Set.range P.1.base ⊆ Z := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_factorsThrough_opens_schemeKer_iff_nsmulPt_eq_one_and_range_subset.solution
