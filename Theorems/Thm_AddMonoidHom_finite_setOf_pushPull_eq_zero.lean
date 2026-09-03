import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_finite_setOf_pushPull_eq_zero

set_option autoImplicit false

theorem AddMonoidHom.finite_setOf_pushPull_eq_zero {M : Type*} [AddCommGroup M] (p : ℕ) (F V δ δ' : M →+ M)
    (hFV : F.comp V = p • AddMonoidHom.id M) (hVF : V.comp F = p • AddMonoidHom.id M)
    (hδδ' : δ.comp δ' = AddMonoidHom.id M) (hδ'δ : δ'.comp δ = AddMonoidHom.id M)
    (hFδ : F.comp δ = δ.comp F) (hVδ : V.comp δ = δ.comp V) (hFδ' : F.comp δ' = δ'.comp F) (hVδ' : V.comp δ' = δ'.comp V)
    (h1 : {x | x - δ (F (F x)) = 0}.Finite) (h2 : {x | x - δ' (V (V x)) = 0}.Finite) :
    {ab : M × M | (1 + p) • ab.1 + (V ab.2 + F (δ ab.2)) = 0 ∧ (F ab.1 + δ' (V ab.1)) + (1 + p) • ab.2 = 0}.Finite := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_finite_setOf_pushPull_eq_zero.solution
