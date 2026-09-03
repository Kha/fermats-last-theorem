import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AutomorphicForm_GaussTwist
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_fnTwist_gaussSumFn_level_invariant
attribute [-instance] HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions
attribute [-simp] AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add
open NumberField AutomorphicForm

theorem LanglandsTunnell.fnTwist_gaussSumFn_level_invariant
    (F : Type) [Field F] [NumberField F]
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥)
    (hmod : HeckeCharacter.AdmitsModulus F η 𝔣)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hinv : ∀ g, ∀ u ∈ (productionPinsCompact F).U N, φ (g * u) = φ g)
    (g : AdelicGL2 (𝓞 F) F)
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ (productionPinsCompact F).U (N * 𝔣 ^ 2)) :
    fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ) (g * k)
      = fnTwist F η (AutomorphicForm.GaussTwist.gaussSumFn F η 𝔣 φ) g := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_fnTwist_gaussSumFn_level_invariant.solution
