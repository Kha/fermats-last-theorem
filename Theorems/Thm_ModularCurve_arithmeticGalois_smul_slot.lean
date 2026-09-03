import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_arithmeticGalois_smul_slot
attribute [-simp] ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.jqNModC_one

open ModularCurve AlgebraicCurve

theorem ModularCurve.arithmeticGalois_smul_slot (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N]
    (ζ : Kˣ) (a b c : ℕ) [NeZero a]
    (σ : K ≃ₐ[ℚ] K) (hσ : σ (ζ : K) = (ζ : K) ^ c)
    (ι : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
        qExpand K N (coeffEmb K jq))
    (hι₂ : ι ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
        qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))
    (w : Place K (laurentBaseChange K (modularFunctionFieldFull N))) (γ : ℤ)
    (hw : ∀ x, w.ord x * γ = (ι x).order) :
    ∃ ι' : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K,
      ι' ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
          qExpand K N (coeffEmb K jq) ∧
      ι' ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
          qExpand K (a * a) (qTwist (ζ ^ (c * b * a)) (coeffEmb K jq)) ∧
      ∀ x, (arithmeticGalois (modularFunctionFieldFull N) σ • w).ord x * γ = (ι' x).order := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_arithmeticGalois_smul_slot.solution
