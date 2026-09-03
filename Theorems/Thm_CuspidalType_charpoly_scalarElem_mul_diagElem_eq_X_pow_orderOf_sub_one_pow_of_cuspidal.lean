import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_charpoly_scalarElem_mul_diagElem_eq_X_pow_orderOf_sub_one_pow_of_cuspidal

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.charpoly_scalarElem_mul_diagElem_eq_X_pow_orderOf_sub_one_pow_of_cuspidal
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (GL2 q) V)
    (hfin : Module.finrank K V = q - 1)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id)
    (z a : (ZMod q)ˣ) (ha : a ≠ 1) :
    LinearMap.charpoly (ρ (scalarElem q z * diagElem q a)) = (X ^ orderOf a - 1) ^ ((q - 1) / orderOf a) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_charpoly_scalarElem_mul_diagElem_eq_X_pow_orderOf_sub_one_pow_of_cuspidal.solution
