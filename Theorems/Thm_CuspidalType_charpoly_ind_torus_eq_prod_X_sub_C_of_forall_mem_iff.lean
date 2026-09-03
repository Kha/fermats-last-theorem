import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_charpoly_ind_torus_eq_prod_X_sub_C_of_forall_mem_iff

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.charpoly_ind_torus_eq_prod_X_sub_C_of_forall_mem_iff
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (S : Finset ((GaloisField q 2)ˣ →* Kˣ))
    (hS : ∀ μ : (GaloisField q 2)ˣ →* Kˣ,
      μ ∈ S ↔ ∀ c : (ZMod q)ˣ, μ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1)
    (α : (GaloisField q 2)ˣ) :
    LinearMap.charpoly (ind q K (torus q α)) = ∏ μ ∈ S, (X - C ((μ α : Kˣ) : K)) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_charpoly_ind_torus_eq_prod_X_sub_C_of_forall_mem_iff.solution
