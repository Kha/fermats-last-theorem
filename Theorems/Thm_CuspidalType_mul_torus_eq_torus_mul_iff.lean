import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_mul_torus_eq_torus_mul_iff

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.mul_torus_eq_torus_mul_iff (q : ℕ) [Fact q.Prime] {α : (GaloisField q 2)ˣ}
    (hα : (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))) (h : GL2 q) :
    h * torus q α = torus q α * h ↔ h ∈ (torus q).range := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_mul_torus_eq_torus_mul_iff.solution
