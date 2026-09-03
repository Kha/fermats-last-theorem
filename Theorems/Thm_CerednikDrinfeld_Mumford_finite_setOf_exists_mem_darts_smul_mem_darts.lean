import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_finite_setOf_exists_mem_darts_smul_mem_darts

set_option autoImplicit false

open CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.finite_setOf_exists_mem_darts_smul_mem_darts
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hfin : ∀ w : W, Finite (stabilizer G w))
    {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    {γ : G | ∃ d ∈ Q.darts, γ • d ∈ P.darts ∨ (γ • d).symm ∈ P.darts}.Finite := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_finite_setOf_exists_mem_darts_smul_mem_darts.solution
