import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg

theorem MonoidAlgebra.mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg
    (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
    (B : Subalgebra (GaloisRep.ratLocalizedAt p) (MonoidAlgebra ℚ (Multiplicative (ZMod q))))
    (hfg : B.FG)
    (haug : ∀ b ∈ B, Coalgebra.counit (R := ℚ) b ∈ GaloisRep.ratLocalizedAt p)
    (hsat : ∀ v : MonoidAlgebra ℚ (Multiplicative (ZMod q)), ∃ n : ℕ, 0 < n ∧ (n : ℚ) • v ∈ B)
    (hadams : ∀ a : ℕ, a.Coprime q → ∀ b ∈ B,
      MonoidAlgebra.mapDomainAlgHom ℚ ℚ (powMonoidHom a) b ∈ B)
    (hinf : ¬ (Subalgebra.toSubmodule B).FG) :
    ∀ v : MonoidAlgebra ℚ (Multiplicative (ZMod q)),
      v ∈ B ↔ Coalgebra.counit (R := ℚ) v ∈ GaloisRep.ratLocalizedAt p := by p2m_exact_reverting @_root_.P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.solution
