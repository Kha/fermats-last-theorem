import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical

open MvPowerSeries

universe u v w

theorem MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (J : Ideal S) [IsAdicComplete J S]
    {σ : Type w} [Finite σ] (ψ : MvPowerSeries σ R →ₐ[R] S)
    (hψ : ∀ s, ψ (X s) ∈ J.radical) (f : MvPowerSeries σ R) :
    ψ f = MvFormalGroup.adicEval J (fun s => ψ (X s)) f := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical.solution
