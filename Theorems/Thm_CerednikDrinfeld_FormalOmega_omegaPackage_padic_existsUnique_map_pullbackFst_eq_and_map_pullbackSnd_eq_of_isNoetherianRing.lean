import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_OmegaModuliPackage
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_omegaPackage_padic_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.omegaPackage_padic_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing
    (p : ℕ) [Fact p.Prime] (π : ℤ_[p]) {O : Type} [CommRing O] (c : ℤ_[p] →+* O)
    :
    (∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (_hs' : Function.Surjective φ') (_hs'' : Function.Surjective φ'')
    (_hn' : IsNilpotent (RingHom.ker φ')) (_hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : ModuliPackage.pullbackRing φ' φ''))
    (x' : (omegaPackage (K := ℚ_[p]) p π c).obj B' ψ' hB') (x'' : (omegaPackage (K := ℚ_[p]) p π c).obj B'' ψ'' hB''),
      (omegaPackage (K := ℚ_[p]) p π c).map hB' hB φ' hφ' x' = (omegaPackage (K := ℚ_[p]) p π c).map hB'' hB φ'' hφ'' x'' →
      ∃! z : (omegaPackage (K := ℚ_[p]) p π c).obj (ModuliPackage.pullbackRing φ' φ'')
          (ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
        (omegaPackage (K := ℚ_[p]) p π c).map hP hB' (ModuliPackage.pullbackFst φ' φ'')
            (ModuliPackage.pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
        (omegaPackage (K := ℚ_[p]) p π c).map hP hB'' (ModuliPackage.pullbackSnd φ' φ'')
            (ModuliPackage.pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_omegaPackage_padic_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing.solution
