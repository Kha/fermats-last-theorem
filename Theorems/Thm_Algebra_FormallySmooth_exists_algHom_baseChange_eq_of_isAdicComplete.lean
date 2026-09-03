import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_exists_algHom_baseChange_eq_of_isAdicComplete

universe u v w w'

theorem Algebra.FormallySmooth.exists_algHom_baseChange_eq_of_isAdicComplete
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ)
    {k : Type v} [CommRing k] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (ℛ : Type w) [CommRing ℛ] [Algebra 𝓞 ℛ] [Algebra.FormallySmooth 𝓞 ℛ]
    (Y : Type w') [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
    (χ : TensorProduct 𝓞 k ℛ →ₐ[k] TensorProduct 𝓞 k Y) :
    ∃ x : ℛ →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id k k) x = χ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_exists_algHom_baseChange_eq_of_isAdicComplete.solution
