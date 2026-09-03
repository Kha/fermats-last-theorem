import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import P2M.Util
import P2M.Sol.S_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem FreyPackage.frey_exists_decomposition_branch_swap_of_a_mod_eight
    (P : FreyPackage) (h8 : (P.a : ZMod 8) = 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2) :
    ∃ σ ∈ A.decompositionSubgroup ℚ,
      ∀ x : Submodule.torsionBy ℤ
          ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p,
        ¬ P.freyCurveInt.InZeroComponentAt A
            (x : ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) →
          P.freyCurveInt.InZeroComponentAt A
            ((σ • x + x :
              Submodule.torsionBy ℤ
                ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p) :
              ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight.solution
