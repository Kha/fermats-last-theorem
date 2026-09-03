import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.HasKernelOfDegree.map_of_bijective
    {B B' : Type u} [CommRing B] [CommRing B'] (f : B →+* B') (hf : Function.Bijective f)
    {φ : Series B} {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d) :
    FormalODModule.HasKernelOfDegree (φ.map f) d := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective.solution
