import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.FormalODModule.isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing
    {q : ℕ} [Fact q.Prime]
    (O : Type) [CommRing O] [IsLocalRing O]
    (ι : Zp2 q →+* O) (X₀ : SpecialFormalODModule q ((IsLocalRing.residue O).comp ι))
    (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
    (resA : A →+* IsLocalRing.ResidueField O) (hs : Function.Surjective resA)
    (hc : resA.comp (algebraMap O A) = IsLocalRing.residue O)
    (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso) :
    X.IsSpecial ((algebraMap O A).comp ι) ∧ X.HasHeight 4 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing.solution
