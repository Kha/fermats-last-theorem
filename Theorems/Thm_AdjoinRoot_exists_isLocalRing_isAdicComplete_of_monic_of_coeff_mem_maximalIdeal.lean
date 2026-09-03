import Mathlib
import P2M.Util
import P2M.Sol.S_AdjoinRoot_exists_isLocalRing_isAdicComplete_of_monic_of_coeff_mem_maximalIdeal

set_option autoImplicit false

open IsLocalRing Polynomial

theorem AdjoinRoot.exists_isLocalRing_isAdicComplete_of_monic_of_coeff_mem_maximalIdeal
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    (g : S[X]) (hg : g.Monic) (hn : 1 ≤ g.natDegree)
    (hcoeff : ∀ i < g.natDegree, g.coeff i ∈ maximalIdeal S) :
    ∃ (_ : IsLocalRing (AdjoinRoot g)),
      IsAdicComplete (maximalIdeal (AdjoinRoot g)) (AdjoinRoot g) ∧
      IsNoetherianRing (AdjoinRoot g) ∧ Module.Finite S (AdjoinRoot g) ∧
      Function.Surjective (⇑(residue (AdjoinRoot g)) ∘ ⇑(algebraMap S (AdjoinRoot g))) ∧
      AdjoinRoot.root g ∈ maximalIdeal (AdjoinRoot g) ∧
      maximalIdeal (AdjoinRoot g) =
        (maximalIdeal S).map (algebraMap S (AdjoinRoot g)) ⊔ Ideal.span {AdjoinRoot.root g} := by p2m_exact_reverting @_root_.P2MW.S_AdjoinRoot_exists_isLocalRing_isAdicComplete_of_monic_of_coeff_mem_maximalIdeal.solution
