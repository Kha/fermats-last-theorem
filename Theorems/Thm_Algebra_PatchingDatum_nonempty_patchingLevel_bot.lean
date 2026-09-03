import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import P2M.Util
import P2M.Sol.S_Algebra_PatchingDatum_nonempty_patchingLevel_bot

theorem Algebra.PatchingDatum.nonempty_patchingLevel_bot
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    {ℓ r : ℕ} (hℓ : (ℓ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {R : Type} [CommRing R] [Algebra 𝒪 R] {M : Type} [AddCommGroup M] [Module R M]
    (P : Algebra.PatchingDatum 𝒪 ℓ r R M) :
    Nonempty (Algebra.PatchingLevel 𝒪 r R M ⊥) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_PatchingDatum_nonempty_patchingLevel_bot.solution
