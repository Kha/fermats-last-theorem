import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Mathlib.GroupTheory.Abelianization.Defs
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq

set_option autoImplicit false

p2m_open "CerednikDrinfeld CerednikDrinfeld.Mumford~surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle MulAction"

theorem CerednikDrinfeld.Mumford.exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hT : 𝒯.IsTree)
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)]
    {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (eV : V ≃ QuotVert G W)
    (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
    (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)
    (v₀ : W)
    (Φ : Additive (Abelianization G) →+ ↥(ribbonKernel D))
    (hΦ : ∀ g : G, (Φ (Additive.ofMul (Abelianization.of g)) : E → ℤ) = pathCycle 𝒯 (fun e => (eE e).1) v₀ g)
    (A : Type) [CommGroup A] (hdiv : ∀ (a : A) (n : ℕ), n ≠ 0 → ∃ b : A, b ^ n = a)
    (c : G →* A) (hc : ∀ (w : W) (g : G), g ∈ stabilizer G w → c g = 1) :
    ∃ ν : E → A, ∀ g : G, c g = ∏ e : E, ν e ^ ((Φ (Additive.ofMul (Abelianization.of g)) : E → ℤ) e) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq.solution
