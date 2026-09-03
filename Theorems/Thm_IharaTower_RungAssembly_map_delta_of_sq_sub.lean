import Mathlib
import P2M.Util
import P2M.Sol.S_IharaTower_RungAssembly_map_delta_of_sq_sub

set_option autoImplicit false

theorem IharaTower.RungAssembly.map_delta_of_sq_sub {𝒪 : Type} [CommRing 𝒪] {T : Type} [CommRing T] [Algebra 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (a t Δ : T) (p nu nl nq n1 : ℕ)
    (hnu : nu = 1) (hnl : nl = 1) (hnq : nq = p + 1) (hn1 : n1 = p + 1)
    (hαq : a * a - t * a + algebraMap 𝒪 T (p : 𝒪) = 0)
    (hΔ : Δ = a ^ 2 * (algebraMap 𝒪 T (nu : 𝒪) * t) - a * (algebraMap 𝒪 T (nq : 𝒪) + algebraMap 𝒪 T (n1 : 𝒪))
        + algebraMap 𝒪 T (nl : 𝒪) * t) :
    πT Δ = (πT a - πT (t - a)) * (πT a ^ 2 - 1) := by p2m_exact_reverting @_root_.P2MW.S_IharaTower_RungAssembly_map_delta_of_sq_sub.solution
