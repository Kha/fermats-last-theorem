import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

theorem Algebra.exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [Algebra.Smooth k B]
    {B' : Type u} [CommRing B'] [Algebra k B'] (ψ : B →ₐ[k] B') (hψ : Function.Surjective ψ)
    (v' : Ideal B') [v'.IsPrime] (v : Ideal B) [v.IsPrime] (hv' : v'.comap ψ.toRingHom = v)
    (hsm : Algebra.IsSmoothAt k v')
    (hrank : Module.finrank v.ResidueField (v.ResidueField ⊗[B] Ω[B⁄k]) ≤
      Module.finrank v'.ResidueField (v'.ResidueField ⊗[B'] Ω[B'⁄k])) :
    ∃ t : B, t ∉ v ∧ (RingHom.ker ψ.toRingHom).map (algebraMap B (Localization.Away t)) = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le.solution
