import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isNilpotent_maximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isNilpotent_maximalIdeal
    (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (D : Type) [CommRing D] [IsLocalRing D] [Algebra V D] [IsLocalHom (algebraMap V D)] [Module.Flat V D]
    (hVD : (maximalIdeal V).map (algebraMap V D) = maximalIdeal D)
    [Module.Finite (ResidueField V) (ResidueField D)] [Algebra.IsSeparable (ResidueField V) (ResidueField D)]
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra V T] (hT : IsNilpotent (maximalIdeal T))
    (ι : ResidueField D →+* ResidueField T)
    (hι : ∀ v : V, ι (residue D (algebraMap V D v)) = residue T (algebraMap V T v)) :
    ∃! g : D →ₐ[V] T, ∀ d : D, residue T (g d) = ι (residue D d) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isNilpotent_maximalIdeal.solution
