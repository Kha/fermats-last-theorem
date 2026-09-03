import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_existsUnique_eq_smul_kaehlerDifferential_D_of_formallySmooth_of_maximalIdeal_eq_map_sup_span

set_option autoImplicit false

open IsLocalRing

theorem RingHom.existsUnique_eq_smul_kaehlerDifferential_D_of_formallySmooth_of_maximalIdeal_eq_map_sup_span
    {A : Type} [CommRing A] [IsLocalRing A]
    {S : Type} [CommRing S] [IsLocalRing S]
    (i : A →+* S) (hi : i.FormallySmooth) (hif : i.EssFiniteType)
    (hres : Function.Surjective ((IsLocalRing.residue S).comp i))
    (t : S) (hm : maximalIdeal S = (maximalIdeal A).map i ⊔ Ideal.span {t})
    (ht : t ∉ (maximalIdeal A).map i) :
    letI : Algebra A S := i.toAlgebra
    ∀ ω : KaehlerDifferential A S, ∃! s : S, ω = s • KaehlerDifferential.D A S t := by p2m_exact_reverting @_root_.P2MW.S_RingHom_existsUnique_eq_smul_kaehlerDifferential_D_of_formallySmooth_of_maximalIdeal_eq_map_sup_span.solution
