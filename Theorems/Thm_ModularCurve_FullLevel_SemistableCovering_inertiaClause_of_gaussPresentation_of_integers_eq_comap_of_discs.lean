import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_SemistableCovering_inertiaClause_of_gaussPresentation_of_integers_eq_comap_of_discs
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel AlgebraicCurve IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.inertiaClause_of_gaussPresentation_of_integers_eq_comap_of_discs
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (hA : A.LiesOverPrime q) (hqM' : ¬ q ∣ M')
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (𝒞 : SemistableCovering q M' A W) (ζ : Idx q)

    (hO : ∀ f : fieldBar q M', f ∈ (𝒞.CIg (lineInfty q)).integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hℓ : ∀ ℓ : CuspidalType.ProjLine q, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧
      (𝒞.CIg ℓ).integers = ((𝒞.CIg (lineInfty q)).integers).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)

    (hIg_discs : ∀ ℓ : CuspidalType.ProjLine q,
      ∃ (N : Finset (Place (ResidueField A) (𝒞.FIg ℓ)))
        (disc : Place (ResidueField A) (𝒞.FIg ℓ) → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
        (∀ P, P ∈ (𝒞.CIg ℓ).dom ↔ ∃ Q, Q ∉ N ∧ P ∈ disc Q) ∧
        (∀ P Q, Q ∉ N → P ∈ disc Q → (𝒞.CIg ℓ).placeMap P = Q) ∧
        (∀ P P', P ∉ (𝒞.CIg ℓ).dom → P' ∉ (𝒞.CIg ℓ).dom → (𝒞.CIg ℓ).placeMap P = (𝒞.CIg ℓ).placeMap P') ∧
        (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
          ∀ Q, Q ∉ N → ∀ P, P ∈ disc Q ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ disc Q))

    (hSS_ind : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ s : ↥W, InducesOnChart (𝒞.CSS s) (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) (RingEquiv.refl _))
    (hSS_discs : ∀ s : ↥W,
      ∃ (N : Finset (Place (ResidueField A) (𝒞.FSS s)))
        (disc : Place (ResidueField A) (𝒞.FSS s) → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
        (∀ P, P ∈ (𝒞.CSS s).dom ↔ ∃ Q, Q ∉ N ∧ P ∈ disc Q) ∧
        (∀ P Q, Q ∉ N → P ∈ disc Q → (𝒞.CSS s).placeMap P = Q) ∧
        (∀ P P', P ∉ (𝒞.CSS s).dom → P' ∉ (𝒞.CSS s).dom → (𝒞.CSS s).placeMap P = (𝒞.CSS s).placeMap P') ∧
        (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
          ∀ Q, Q ∉ N → ∀ P, P ∈ disc Q ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ disc Q))

    (hAn_dom : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W) (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')),
        P ∈ (𝒞.An ℓ s).dom ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ (𝒞.An ℓ s).dom)
    (hAn_param : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (𝒞.An ℓ s).param = (𝒞.An ℓ s).param)
    (hAn'_param : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (𝒞.An' ℓ s).param = (𝒞.An' ℓ s).param) :
    𝒞.InertiaClause π := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_SemistableCovering_inertiaClause_of_gaussPresentation_of_integers_eq_comap_of_discs.solution
