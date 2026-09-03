import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_map_colon_eq_colon_map_of_flat
set_option autoImplicit false

theorem Ideal.map_colon_eq_colon_map_of_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I J : Ideal R) (hJ : J.FG) :
    (Submodule.colon I (J : Set R)).map (algebraMap R S)
      = Submodule.colon (I.map (algebraMap R S)) (J.map (algebraMap R S) : Set S) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_map_colon_eq_colon_map_of_flat.solution
