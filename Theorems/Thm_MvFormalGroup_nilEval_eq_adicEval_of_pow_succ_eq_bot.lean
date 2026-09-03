import Mathlib
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot

set_option autoImplicit false

theorem MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot
    {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ]
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (φ : MvPowerSeries σ B) (s : σ → B') (hs : ∀ i, s i ∈ J) :
    MvFormalGroup.nilEval n φ s = MvFormalGroup.adicEval J s φ := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot.solution
