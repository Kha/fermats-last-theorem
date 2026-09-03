import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing
open scoped Quaternion TensorProduct NumberField

universe u

theorem GoodReductionJacobian.BareDeformation.exists_schemeKer_comparison
    {S B : Type} [CommRing S] [CommRing B] [Algebra B S]
    {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
    (D : BareDeformation fₛ Lₛ B) (n : ℕ) :
    ∃ gK : Lₛ.schemeKer n ⟶ D.L.schemeKer n,
      gK ≫ pullback.fst (D.L.schemeNsmul n) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1 =
        pullback.fst (Lₛ.schemeNsmul n) (Lₛ.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ D.g ∧
      IsPullback gK (Lₛ.schemeKerStr n) (D.L.schemeKerStr n)
        (Spec.map (CommRingCat.ofHom (algebraMap B S))) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison.solution
