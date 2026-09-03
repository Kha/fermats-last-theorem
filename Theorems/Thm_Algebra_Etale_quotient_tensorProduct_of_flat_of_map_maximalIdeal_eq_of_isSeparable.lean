import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_quotient_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_isSeparable

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem Algebra.Etale.quotient_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_isSeparable
    (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (D : Type) [CommRing D] [IsLocalRing D] [Algebra V D] [IsLocalHom (algebraMap V D)] [Module.Flat V D]
    (hVD : (maximalIdeal V).map (algebraMap V D) = maximalIdeal D)
    [Module.Finite (ResidueField V) (ResidueField D)] [Algebra.IsSeparable (ResidueField V) (ResidueField D)]
    (m : ℕ) (hm : 0 < m) :
    Algebra.Etale (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_quotient_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_isSeparable.solution
