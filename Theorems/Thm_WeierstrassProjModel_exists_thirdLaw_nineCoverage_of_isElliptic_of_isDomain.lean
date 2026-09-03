import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.RingTheory.Noetherian.Defs
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_thirdLaw_nineCoverage_of_isElliptic_of_isDomain
attribute [-simp] WeierstrassProjModel.kw_lrThird_substHom_X

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))
theorem WeierstrassProjModel.exists_thirdLaw_nineCoverage_of_isElliptic_of_isDomain
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] :
    ∃ (u₃ : ∀ (i j : Fin 3), Fin 3 → (𝒜 i) ⊗[R] (𝒜 j))
      (toE₃ : ∀ (i j k : Fin 3),
        Spec (CommRingCat.of (Localization.Away (u₃ i j k))) ⟶ projModelCR W.toProjective),
      (∀ i j, Ideal.span (Set.range (kw_lrSixU W i j) ∪ Set.range (u₃ i j))
        = (⊤ : Ideal ((𝒜 i) ⊗[R] (𝒜 j)))) ∧
      (∀ (i j k : Fin 3) (l : Fin 3 ⊕ Fin 3),
        pullback.fst
            (Spec.map (CommRingCat.ofHom
              (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ i j k)))))
            (kw_lrSixU_locMap W i j l)
          ≫ toE₃ i j k
        = pullback.snd
            (Spec.map (CommRingCat.ofHom
              (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ i j k)))))
            (kw_lrSixU_locMap W i j l)
          ≫ kw_lrSixU_toE W i j l) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_thirdLaw_nineCoverage_of_isElliptic_of_isDomain.solution
