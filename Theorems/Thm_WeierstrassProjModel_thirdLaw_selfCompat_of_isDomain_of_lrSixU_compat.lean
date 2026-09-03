import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat

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
theorem WeierstrassProjModel.thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat
    (i j : Fin 3) [IsDomain ((𝒜 i) ⊗[R] (𝒜 j))]
    (hne : ∃ l, kw_lrSixU W i j l ≠ 0)
    (u₃ : Fin 3 → (𝒜 i) ⊗[R] (𝒜 j))
    (toE₃ : ∀ k : Fin 3,
      Spec (CommRingCat.of (Localization.Away (u₃ k))) ⟶ projModelCR W.toProjective)
    (hcompat₃ : ∀ (k : Fin 3) (l : Fin 3 ⊕ Fin 3),
      pullback.fst
          (Spec.map (CommRingCat.ofHom
            (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k)))))
          (kw_lrSixU_locMap W i j l)
        ≫ toE₃ k
      = pullback.snd
          (Spec.map (CommRingCat.ofHom
            (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k)))))
          (kw_lrSixU_locMap W i j l)
        ≫ kw_lrSixU_toE W i j l)
    (k k' : Fin 3) :
    pullback.fst
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k)))))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k')))))
      ≫ toE₃ k
    = pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k)))))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k')))))
      ≫ toE₃ k' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat.solution
