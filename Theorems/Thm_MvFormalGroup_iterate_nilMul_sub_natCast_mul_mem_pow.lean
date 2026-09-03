import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_MvFormalGroup_iterate_nilMul_sub_natCast_mul_mem_pow

set_option autoImplicit false

open MvFormalGroup

theorem MvFormalGroup.iterate_nilMul_sub_natCast_mul_mem_pow
    {B : Type} [CommRing B] {g : ℕ} (F : MvFormalGroup g B)
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (ν : ℕ) (hJ : J ^ (ν + 1) = ⊥)
    (k : ℕ) (hk : 1 ≤ k) (s : Fin g → B') (hs : ∀ i, s i ∈ J ^ k) (m : ℕ) (i : Fin g) :
    ((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) i - (m : B') * s i ∈ J ^ (k + 1) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_iterate_nilMul_sub_natCast_mul_mem_pow.solution
