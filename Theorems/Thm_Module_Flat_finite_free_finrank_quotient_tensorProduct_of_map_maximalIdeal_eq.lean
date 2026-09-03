import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem Module.Flat.finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq
    (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (D : Type) [CommRing D] [IsLocalRing D] [Algebra V D] [IsLocalHom (algebraMap V D)] [Module.Flat V D]
    (hVD : (maximalIdeal V).map (algebraMap V D) = maximalIdeal D)
    [Module.Finite (ResidueField V) (ResidueField D)]
    (m : ℕ) (hm : 0 < m) :
    Module.Finite (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) ∧ Module.Free (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) ∧
      Module.finrank (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) = Module.finrank (ResidueField V) (ResidueField D) := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq.solution
