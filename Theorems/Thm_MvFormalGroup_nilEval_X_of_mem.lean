import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_MvFormalGroup_nilEval_X_of_mem

set_option autoImplicit false

open MvPowerSeries

theorem MvFormalGroup.nilEval_X_of_mem
    {σ : Type} [Fintype σ] [DecidableEq σ] {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    (J : Ideal B') (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (s : σ → B') (hs : ∀ i, s i ∈ J) (i : σ) :
    MvFormalGroup.nilEval n (MvPowerSeries.X i : MvPowerSeries σ B) s = s i := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_nilEval_X_of_mem.solution
