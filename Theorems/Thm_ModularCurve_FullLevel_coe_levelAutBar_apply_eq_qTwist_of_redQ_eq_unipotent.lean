import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qTwist_of_redQ_eq_unipotent

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.coe_levelAutBar_apply_eq_qTwist_of_redQ_eq_unipotent
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (hγu : ∃ t : ZMod q, redQ q γ = CuspidalType.unipotent q t)
    (u : (AlgebraicClosure ℚ)ˣ) (hu : (u : AlgebraicClosure ℚ) = ζ.val)
    (f : fieldBar q M') :
    ((levelAutBar q M' ζ γ f : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.qTwist (u ^ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1))
        (f : LaurentSeries (AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qTwist_of_redQ_eq_unipotent.solution
