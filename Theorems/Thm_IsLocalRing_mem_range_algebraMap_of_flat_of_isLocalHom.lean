import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom

set_option autoImplicit false

universe u v u' v'

theorem IsLocalRing.mem_range_algebraMap_of_flat_of_isLocalHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsDomain R] [IsDomain S]
    (f : R →+* S) (hf : f.Flat) [IsLocalHom f]
    (K : Type u') (L : Type v') [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (hcomm : ∀ r : R, algebraMap R L r = algebraMap S L (f r))
    (x : K) (hx : algebraMap K L x ∈ (algebraMap S L).range) :
    x ∈ (algebraMap R K).range := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom.solution
