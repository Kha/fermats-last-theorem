import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_algebraicIndependent_residue_of_le_trdeg

set_option autoImplicit false

universe u v

theorem ValuationSubring.exists_algebraicIndependent_residue_of_le_trdeg
    {k : Type u} {K : Type v} [Field k] [Field K] (c : k →+* K) (O : ValuationSubring K)
    (hc : ∀ x : k, c x ∈ O) {d : ℕ}
    (hd :
      letI : Algebra k (IsLocalRing.ResidueField O) :=
        ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
      (d : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField O)) :
    ∃ (g : Fin d → K) (hg : ∀ i, g i ∈ O),
      letI : Algebra k (IsLocalRing.ResidueField O) :=
        ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
      AlgebraicIndependent k (fun i => IsLocalRing.residue O ⟨g i, hg i⟩) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_algebraicIndependent_residue_of_le_trdeg.solution
