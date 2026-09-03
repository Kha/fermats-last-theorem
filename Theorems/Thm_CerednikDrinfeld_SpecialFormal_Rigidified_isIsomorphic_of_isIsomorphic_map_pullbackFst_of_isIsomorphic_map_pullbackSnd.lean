import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isIsomorphic_map_pullbackFst_of_isIsomorphic_map_pullbackSnd

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_isIsomorphic_map_pullbackFst_of_isIsomorphic_map_pullbackSnd
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p O)).comp ι)) (hΦ4 : Φ.HasHeight 4)
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (hs' : Function.Surjective φ') (hs'' : Function.Surjective φ'')
    (hn' : IsNilpotent (RingHom.ker φ')) (hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : ModuliPackage.pullbackRing φ' φ''))
    (ψP : O →+* ModuliPackage.pullbackRing φ' φ'')
    (hψP' : (ModuliPackage.pullbackFst φ' φ'').comp ψP = ψ')
    (hψP'' : (ModuliPackage.pullbackSnd φ' φ'').comp ψP = ψ'')
    (t₁ t₂ : Rigidified p Φ (ModuliPackage.pullbackRing φ' φ''))
    (h₁ : t₁.IsAdmissible ι ψP) (h₂ : t₂.IsAdmissible ι ψP)
    (h' : (t₁.map (ModuliPackage.pullbackFst φ' φ'')).IsIsomorphic (t₂.map (ModuliPackage.pullbackFst φ' φ'')))
    (h'' : (t₁.map (ModuliPackage.pullbackSnd φ' φ'')).IsIsomorphic (t₂.map (ModuliPackage.pullbackSnd φ' φ''))) :
    t₁.IsIsomorphic t₂ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isIsomorphic_map_pullbackFst_of_isIsomorphic_map_pullbackSnd.solution
