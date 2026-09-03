import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_pi_and_finitePresentation_pi_of_span_eq_top

set_option autoImplicit false

theorem Module.FaithfullyFlat.pi_and_finitePresentation_pi_of_span_eq_top
    {S : Type} [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → S) (hg : Ideal.span (Set.range g) = ⊤)
    (C : ι → Type) [∀ i, CommRing (C i)] [∀ i, Algebra S (C i)] [∀ i, Algebra (Localization.Away (g i)) (C i)]
    [∀ i, IsScalarTower S (Localization.Away (g i)) (C i)]
    (hff : ∀ i, Module.FaithfullyFlat (Localization.Away (g i)) (C i))
    (hfp : ∀ i, Algebra.FinitePresentation (Localization.Away (g i)) (C i)) :
    Module.FaithfullyFlat S (∀ i, C i) ∧ Algebra.FinitePresentation S (∀ i, C i) := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_pi_and_finitePresentation_pi_of_span_eq_top.solution
