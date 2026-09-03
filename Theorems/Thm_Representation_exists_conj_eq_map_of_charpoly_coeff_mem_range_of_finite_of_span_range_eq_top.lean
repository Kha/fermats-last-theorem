import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top

universe u v
theorem Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top
    {K : Type v} [Field K] {L : Type u} [Field L] [Algebra K L] [Finite L]
    {n : Type} [DecidableEq n] [Fintype n] [Nonempty n] {G : Type u} [Group G]
    (φ : G →* GL n L)
    (hspan : Submodule.span L (Set.range fun g => (φ g : Matrix n n L)) = ⊤)
    (hcoeff : ∀ g i, (φ g : Matrix n n L).charpoly.coeff i ∈ (algebraMap K L).range) :
    ∃ ρ : G →* GL n ((algebraMap K L).range), ∃ Q : GL n L,
      ∀ g, (Q⁻¹ * φ g * Q : Matrix n n L)
        = (ρ g : Matrix n n ((algebraMap K L).range)).map ((algebraMap K L).range.subtype) := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.solution
