import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import P2M.Util
import P2M.Sol.S_IsLocalHom_algebraMap_quotient_of_ne_top

theorem IsLocalHom.algebraMap_quotient_of_ne_top
    {𝒪 A : Type} [CommRing 𝒪] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [IsLocalHom (algebraMap 𝒪 A)] (I : Ideal A) (hI : I ≠ ⊤) :
    IsLocalHom (algebraMap 𝒪 (A ⧸ I)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalHom_algebraMap_quotient_of_ne_top.solution
