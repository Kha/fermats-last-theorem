import Mathlib
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import P2M.Util
namespace P2MW.S_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution
    {q : ℕ} [Fact q.Prime] (k : Type*) [Field k] [CharP k q] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (v : Place k (modularFunctionFieldC k N)) (hv : IsAffineGeomPlace k N v) :
    IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · show (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ _
    rw [mem_frobOnPlacesGeomLevel_iff k N data hKr v, frobeniusGeomLevel_jq k N data hKr]
    exact pow_mem h1 q
  · show (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ∈ _
    rw [mem_frobOnPlacesGeomLevel_iff k N data hKr v, frobeniusGeomLevel_jqN k N data hKr]
    exact pow_mem h2 q
