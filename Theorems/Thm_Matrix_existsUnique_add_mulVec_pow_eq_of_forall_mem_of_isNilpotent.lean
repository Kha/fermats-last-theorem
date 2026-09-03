import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent

universe u

theorem Matrix.existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    {d : ℕ} (𝔫 : Ideal S) (h𝔫 : IsNilpotent 𝔫)
    (D : Matrix (Fin d) (Fin d) S) (hD : ∀ i j : Fin d, j ≤ i → D i j ∈ 𝔫)
    (b : Fin d → S) :
    ∃! y : Fin d → S, y + D.mulVec (fun j => y j ^ p) = b := by p2m_exact_reverting @_root_.P2MW.S_Matrix_existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent.solution
