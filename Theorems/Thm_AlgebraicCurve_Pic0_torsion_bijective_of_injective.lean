import Definitions.Def_AlgebraicCurve_JacobianH1Autoduality
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_torsion_bijective_of_injective

theorem AlgebraicCurve.Pic0.torsion.bijective_of_injective {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n] [Finite (Pic0.torsion K F n)] (f : Pic0.torsion K F n →+ Additive (HomPic0Gm K F n)) (hf : Function.Injective f) :
    Function.Bijective f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_torsion_bijective_of_injective.solution
