import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_sum_unipotent_mul_apply_apply_eq_zero_of_forall_unipotent_apply_eq

set_option autoImplicit false

theorem CuspidalType.sum_unipotent_mul_apply_apply_eq_zero_of_forall_unipotent_apply_eq
    (q : ℕ) [Fact q.Prime] (K : Type) [CommRing K] {W : Type} [AddCommGroup W] [Module K W]
    (σ : Representation K (CuspidalType.GL2 q) W)
    (hN : ∀ w : W, (∀ t : ZMod q, σ (CuspidalType.unipotent q t) w = w) → w = 0)
    (V' : Type) [AddCommGroup V'] [Module K V'] (Φ : CuspidalType.GL2 q →* Module.End K V')
    (f : W →ₗ[K] V') (hf : ∀ x : CuspidalType.GL2 q, f ∘ₗ σ x = Φ x ∘ₗ f) :
    ∀ (w : W) (g : CuspidalType.GL2 q), (∑ t : ZMod q, Φ (CuspidalType.unipotent q t) * Φ g) (f w) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_sum_unipotent_mul_apply_apply_eq_zero_of_forall_unipotent_apply_eq.solution
