import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.Meromorphic.Order
import P2M.Util
import P2M.Sol.S_AutomorphicForm_HeckeEigensystem_hasProd_rsEulerPoly_contragredient_fibre_eq_prod_twist_of_isBaseChangeOf

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open Deep.NTSupply
open scoped Classical

theorem AutomorphicForm.HeckeEigensystem.hasProd_rsEulerPoly_contragredient_fibre_eq_prod_twist_of_isBaseChangeOf
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (η : NarrowRayClassGroup F 𝔣 →* ℂˣ)
    (hη : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ ((w.under (𝓞 F)).asIdeal ∣ 𝔣)),
      orderOf (η (primeClass F 𝔣 (w.under (𝓞 F)) hw)) =
        (w.under (𝓞 F)).asIdeal.inertiaDeg' w.asIdeal)
    (π π' : HeckeEigensystem F ℂ) (Ψ : HeckeEigensystem E ℂ)
    (h : IsBaseChangeOf π Ψ) (h' : IsBaseChangeOf π' Ψ) :
    ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ SF : Finset (HeightOneSpectrum (𝓞 F)), S₂ ⊆ SF →
      ∀ SE : Finset (HeightOneSpectrum (𝓞 E)), (∀ w, w ∈ SE ↔ w.under (𝓞 F) ∈ SF) →
        ∀ (s : ℂ) (LE : ℂ) (L : Fin (Module.finrank F E) → ℂ),
          HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ SE} =>
            ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Ψ.a w.1 / Ψ.b w.1) (Ψ.b w.1)⁻¹ (Ψ.a w.1) (Ψ.b w.1) 0).eval
              (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) LE →
          (∀ i : Fin (Module.finrank F E),
            HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ SF} =>
              ((LanglandsTunnell.RankinSelberg.rsEulerPoly
                  ((π.twist (fun v => if hv : ¬ v.asIdeal ∣ 𝔣 then (((η ^ (i : ℕ)) (primeClass F 𝔣 v hv) : ℂˣ) : ℂ) else 0)).a v.1 /
                    (π.twist (fun v => if hv : ¬ v.asIdeal ∣ 𝔣 then (((η ^ (i : ℕ)) (primeClass F 𝔣 v hv) : ℂˣ) : ℂ) else 0)).b v.1)
                  ((π.twist (fun v => if hv : ¬ v.asIdeal ∣ 𝔣 then (((η ^ (i : ℕ)) (primeClass F 𝔣 v hv) : ℂˣ) : ℂ) else 0)).b v.1)⁻¹
                  (π'.a v.1) (π'.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (L i)) →
          LE = ∏ i : Fin (Module.finrank F E), L i := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_HeckeEigensystem_hasProd_rsEulerPoly_contragredient_fibre_eq_prod_twist_of_isBaseChangeOf.solution
