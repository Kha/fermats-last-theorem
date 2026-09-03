import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_injective_of_trdeg_le_one_of_exists_transcendental

theorem AlgHom.injective_of_trdeg_le_one_of_exists_transcendental
    {k D L E : Type*} [Field k] [CommRing D] [IsDomain D] [Algebra k D]
    [CommRing L] [IsDomain L] [Algebra k L] [CommRing E] [Algebra k E]
    (Θ : D →ₐ[k] L) (hΘ : Function.Injective Θ) (hL : Algebra.trdeg k L ≤ 1)
    (Ψ : D →ₐ[k] E) (hΨ : ∃ d : D, Transcendental k (Ψ d)) :
    Function.Injective Ψ := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_injective_of_trdeg_le_one_of_exists_transcendental.solution
