import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_localizedModule_mk_eq_of_coord

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open scoped TensorProduct

theorem CerednikDrinfeld.SpecialFormal.Rigidified.localizedModule_mk_eq_of_coord
    {p : ℕ} [Fact p.Prime]
    {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B'] (f : B →ₐ[ℤ_[p]] B')
    (N : Submodule B (Fin 2 → B)) (N' : Submodule B' (Fin 2 → B'))
    (T : Type) [AddCommGroup T] [Module B T] (T' : Type) [AddCommGroup T'] [Module B' T']
    (σ : T ≃ₗ[B] ↥N) (σ' : T' ≃ₗ[B'] ↥N')
    (τ : T →ₛₗ[(f : B →+* B')] T')
    (hτσ : ∀ (r : T) (i : Fin 2), ((σ' (τ r) : ↥N') : Fin 2 → B') i = f (((σ r : ↥N) : Fin 2 → B) i))
    (x' : PrimeSpectrum B') (g : B) (hg : g ∉ (PrimeSpectrum.comap (f : B →+* B') x').asIdeal)
    (hg' : f g ∉ x'.asIdeal)
    (fg : Rigidified.Baway g →+* Rigidified.Baway (f g))
    (hfg : fg.comp (Rigidified.awayHom g) = (Rigidified.awayHom (f g)).comp (f : B →+* B'))
    (tt sQ : T) (s : B) (hs : f s ∉ x'.asIdeal) (b : (PrimeSpectrum.comap (f : B →+* B') x').asIdeal.primeCompl)
    (heq : LocalizedModule.mk tt
        (⟨s, fun h => hs (by simpa using (Ideal.mem_comap.mp h))⟩ : (PrimeSpectrum.comap (f : B →+* B') x').asIdeal.primeCompl) =
      LocalizedModule.mk sQ b)
    (w : Fin 2 → Rigidified.Baway g)
    (hσb : ∀ i, Rigidified.locHom (PrimeSpectrum.comap (f : B →+* B') x') (((σ sQ : ↥N) : Fin 2 → B) i) =
      Rigidified.locHom (PrimeSpectrum.comap (f : B →+* B') x') (b : B) *
        Rigidified.awayToLoc (PrimeSpectrum.comap (f : B →+* B') x') g hg (w i))
    (s' : T') (b' : x'.asIdeal.primeCompl) (w' : Fin 2 → Rigidified.Baway (f g))
    (hσb' : ∀ i, Rigidified.locHom x' (((σ' s' : ↥N') : Fin 2 → B') i) =
      Rigidified.locHom x' (b' : B') * Rigidified.awayToLoc x' (f g) hg' (w' i))
    (hw : ∀ i, w' i = fg (w i)) :
    LocalizedModule.mk s' b' = LocalizedModule.mk (τ tt) (⟨f s, hs⟩ : x'.asIdeal.primeCompl) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_localizedModule_mk_eq_of_coord.solution
