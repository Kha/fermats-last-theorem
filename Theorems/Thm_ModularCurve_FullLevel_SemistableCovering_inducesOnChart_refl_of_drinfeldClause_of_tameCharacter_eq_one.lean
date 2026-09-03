import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_SemistableCovering_inducesOnChart_refl_of_drinfeldClause_of_tameCharacter_eq_one

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup DrinfeldCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.inducesOnChart_refl_of_drinfeldClause_of_tameCharacter_eq_one
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (𝒞 : SemistableCovering q M' A W)
    [Algebra (GaloisField q 2) (ResidueField A)] [IsDomain (CoordRing q (ResidueField A))]
    (π : AlgebraicClosure ℚ) (ι : GaloisField q 2 →+* ResidueField A) (η : ℕ) (ζ : Idx q) (s : ↥W)
    (hD : 𝒞.DrinfeldClause π ι η ζ s) :
    ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      SemistableCovering.InducesOnChart (𝒞.CSS s)
        (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) (RingEquiv.refl _) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_SemistableCovering_inducesOnChart_refl_of_drinfeldClause_of_tameCharacter_eq_one.solution
