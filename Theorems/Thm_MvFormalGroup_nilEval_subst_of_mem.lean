import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_MvFormalGroup_nilEval_subst_of_mem

set_option autoImplicit false

open MvPowerSeries

theorem MvFormalGroup.nilEval_subst_of_mem
    {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    (J : Ideal B') (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (s : τ → B') (hs : ∀ i, s i ∈ J)
    (φ : σ → MvPowerSeries τ B) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (ψ : MvPowerSeries σ B) :
    (∀ j, MvFormalGroup.nilEval n (φ j) s ∈ J) ∧
    MvFormalGroup.nilEval n (MvPowerSeries.subst φ ψ) s =
      MvFormalGroup.nilEval n ψ (fun j => MvFormalGroup.nilEval n (φ j) s) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_nilEval_subst_of_mem.solution
