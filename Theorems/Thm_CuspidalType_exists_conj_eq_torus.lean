import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_exists_conj_eq_torus

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.exists_conj_eq_torus (q : ℕ) [Fact q.Prime] (g : GL2 q)
    (hg : ∀ x : ZMod q, ¬ (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x) :
    ∃ (h : GL2 q) (α : (GaloisField q 2)ˣ),
      (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2)) ∧ h * g * h⁻¹ = torus q α := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_exists_conj_eq_torus.solution
