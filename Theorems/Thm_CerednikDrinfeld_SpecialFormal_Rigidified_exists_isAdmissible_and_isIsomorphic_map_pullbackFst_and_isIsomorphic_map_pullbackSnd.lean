import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_map_pullbackFst_and_isIsomorphic_map_pullbackSnd
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isIsomorphic_map_pullbackFst_and_isIsomorphic_map_pullbackSnd
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
    (t' : Rigidified p Φ B') (t'' : Rigidified p Φ B'')
    (ht' : t'.IsAdmissible ι ψ') (ht'' : t''.IsAdmissible ι ψ'')
    (h : (t'.map φ').IsIsomorphic (t''.map φ'')) :
    ∃ t : Rigidified p Φ (ModuliPackage.pullbackRing φ' φ''),
      t.IsAdmissible ι ψP ∧
      (t.map (ModuliPackage.pullbackFst φ' φ'')).IsIsomorphic t' ∧
      (t.map (ModuliPackage.pullbackSnd φ' φ'')).IsIsomorphic t'' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_map_pullbackFst_and_isIsomorphic_map_pullbackSnd.solution
