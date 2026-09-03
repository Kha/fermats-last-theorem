import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hfin : ∀ w : W, Finite (MulAction.stabilizer G w))
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)]
    {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (eV : V ≃ QuotVert G W)
    (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
    (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)
    (φ : W → ℤ) (hφ : ∀ g : G, ∃ n : ℤ, ∀ w : W, φ (g • w) = φ w + n)
    (hharm : ∀ (u : W) (S : Finset W), (∀ x, x ∈ S ↔ 𝒯.Adj u x) → ∑ x ∈ S, (φ x - φ u) = 0)
    (hdiv : ∀ d : 𝒯.Dart, ((Nat.card (MulAction.stabilizer G d) : ℕ) : ℤ) ∣ φ d.snd - φ d.fst) :
    ∃ c : E → ℤ,
      (∀ e : E, φ (eE e).1.out.snd - φ (eE e).1.out.fst = ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e) ∧
      c ∈ ribbonKernel D ∧
      ∀ (u u' : W) (p : 𝒯.Walk u u'),
        φ u' - φ u = ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e * walkCycle 𝒯 (fun e => (eE e).1) p e := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd.solution
