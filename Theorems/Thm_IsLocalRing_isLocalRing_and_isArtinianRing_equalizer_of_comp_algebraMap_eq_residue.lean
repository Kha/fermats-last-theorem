import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue

set_option autoImplicit false

universe u

open IsLocalRing in

theorem IsLocalRing.isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue
    (O : Type u) [CommRing O] [IsLocalRing O]
    (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
    (resA' : A' →+* ResidueField O) (hc' : resA'.comp (algebraMap O A') = residue O)
    (A'' : Type u) [CommRing A''] [IsLocalRing A''] [IsArtinianRing A''] [Algebra O A'']
    (resA'' : A'' →+* ResidueField O) (hc'' : resA''.comp (algebraMap O A'') = residue O)
    (A : Type u) [CommRing A] [Algebra O A] (resA : A →+* ResidueField O)
    (q' : A' →ₐ[O] A) (hq' : resA.comp q'.toRingHom = resA')
    (q'' : A'' →ₐ[O] A) (hq'' : resA.comp q''.toRingHom = resA'') :
    IsLocalRing ↥(AlgHom.equalizer (q'.comp (AlgHom.fst O A' A'')) (q''.comp (AlgHom.snd O A' A''))) ∧
    IsArtinianRing ↥(AlgHom.equalizer (q'.comp (AlgHom.fst O A' A'')) (q''.comp (AlgHom.snd O A' A''))) ∧
    Function.Surjective (resA'.comp ((AlgHom.fst O A' A'').comp
      (AlgHom.equalizer (q'.comp (AlgHom.fst O A' A'')) (q''.comp (AlgHom.snd O A' A''))).val).toRingHom) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue.solution
