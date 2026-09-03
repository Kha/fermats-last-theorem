import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_Hopf_map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange

universe u v w

open scoped TensorProduct

theorem PDivisibleGroup.Hopf.map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (A : Type w) [CommRing A] [Bialgebra R A] (n : ℕ) :
    Algebra.TensorProduct.map (AlgHom.id S S) (PDivisibleGroup.Hopf.nsmulAlgHom R A n) =
      PDivisibleGroup.Hopf.nsmulAlgHom S (S ⊗[R] A) n := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_Hopf_map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange.solution
