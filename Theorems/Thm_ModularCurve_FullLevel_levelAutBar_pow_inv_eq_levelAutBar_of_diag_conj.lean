import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj (q : ℕ) [Fact q.Prime]
    (M' : ℕ) (hqM' : ¬ q ∣ M') (ζ : ModularCurve.FullLevel.Idx q) (d : (ZMod q)ˣ) (α α' : SL(2, ℤ))
    (hα : α ∈ CongruenceSubgroup.Gamma0 M') (hα' : α' ∈ CongruenceSubgroup.Gamma0 M')
    (h : !![(1 : ZMod q), 0; 0, (d : ZMod q)] * (α : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q)
        = (α' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) * !![(1 : ZMod q), 0; 0, (d : ZMod q)]) :
    ModularCurve.FullLevel.levelAutBar q M' (ζ.pow d⁻¹) α =
      ModularCurve.FullLevel.levelAutBar q M' ζ α' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj.solution
