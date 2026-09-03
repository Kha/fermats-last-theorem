import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_det_ringEquiv_tmul_one_eq_algebraMap_nrd

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

theorem QuaternionAlgebra.det_ringEquiv_tmul_one_eq_algebraMap_nrd
    {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ t : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (x : ℍ[ℚ, a, b]) :
    (φ (x ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))).det = algebraMap ℚ (v.adicCompletion ℚ) (QuaternionAlgebra.nrd x) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_det_ringEquiv_tmul_one_eq_algebraMap_nrd.solution
