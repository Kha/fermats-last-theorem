import Mathlib
import P2M.Util
import P2M.Sol.S_AdjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete

set_option autoImplicit false

universe u

open Polynomial IsLocalRing in

theorem AdjoinRoot.exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete
    (R : Type u) [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (f : R[X]) (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))]
    [Algebra.IsSeparable (ResidueField R) (AdjoinRoot (f.map (residue R)))] :
    ∃ (_ : IsLocalRing (AdjoinRoot f)) (_ : IsLocalHom (algebraMap R (AdjoinRoot f))),
      Module.Finite R (AdjoinRoot f) ∧ Module.Free R (AdjoinRoot f) ∧ Algebra.Etale R (AdjoinRoot f) ∧
      IsAdicComplete (maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) ∧
      Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R) = maximalIdeal (AdjoinRoot f) ∧
      Nonempty (ResidueField (AdjoinRoot f) ≃ₐ[ResidueField R] AdjoinRoot (f.map (residue R))) := by p2m_exact_reverting @_root_.P2MW.S_AdjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete.solution
