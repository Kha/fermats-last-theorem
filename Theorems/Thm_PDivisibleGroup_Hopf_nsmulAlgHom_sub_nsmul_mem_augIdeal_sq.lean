import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_Hopf_nsmulAlgHom_sub_nsmul_mem_augIdeal_sq

set_option autoImplicit false

universe u v

theorem PDivisibleGroup.Hopf.nsmulAlgHom_sub_nsmul_mem_augIdeal_sq
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]
    (n : ℕ) {x : A} (hx : x ∈ PDivisibleGroup.Hopf.augIdeal R A) :
    PDivisibleGroup.Hopf.nsmulAlgHom R A n x - n • x ∈ PDivisibleGroup.Hopf.augIdeal R A ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_Hopf_nsmulAlgHom_sub_nsmul_mem_augIdeal_sq.solution
