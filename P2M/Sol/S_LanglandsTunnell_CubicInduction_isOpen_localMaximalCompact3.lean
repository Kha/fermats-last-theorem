import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import P2M.Util
namespace P2MW.S_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3

set_option autoImplicit false

open IsDedekindDomain

open LanglandsTunnell.CubicInduction

namespace IntegralEntriesOpen

private theorem continuous_entry {A : Type*} [CommRing A] [TopologicalSpace A] (i j : Fin 3) :
    Continuous fun k : GL (Fin 3) A => (k : Matrix (Fin 3) (Fin 3) A) i j :=
  Units.continuous_val.matrix_elem i j

private theorem continuous_inv_entry {A : Type*} [CommRing A] [TopologicalSpace A] (i j : Fin 3) :
    Continuous fun k : GL (Fin 3) A => ((k⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) i j :=
  Units.continuous_coe_inv.matrix_elem i j

private theorem coe_localMaximalCompact3_eq (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    ((LanglandsTunnell.CubicInduction.localMaximalCompact3 R K v :
        Subgroup (GL (Fin 3) (v.adicCompletion K))) : Set (GL (Fin 3) (v.adicCompletion K))) =
      (⋂ i : Fin 3, ⋂ j : Fin 3,
          (fun k : GL (Fin 3) (v.adicCompletion K) => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ⁻¹'
            (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∩
        (⋂ i : Fin 3, ⋂ j : Fin 3,
          (fun k : GL (Fin 3) (v.adicCompletion K) =>
              ((k⁻¹ : GL (Fin 3) (v.adicCompletion K)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ⁻¹'
            (v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
  ext k
  simp only [SetLike.mem_coe, LanglandsTunnell.CubicInduction.mem_localMaximalCompact3_iff, Set.mem_inter_iff,
    Set.mem_iInter, Set.mem_preimage, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]

end IntegralEntriesOpen

open IntegralEntriesOpen

theorem solution
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) :
    IsOpen ((localMaximalCompact3 R K v : Subgroup (GL (Fin 3) (v.adicCompletion K))) :
      Set (GL (Fin 3) (v.adicCompletion K))) := by
  have hO : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isOpen_valuationSubring _
  rw [coe_localMaximalCompact3_eq R K v]
  refine IsOpen.inter ?_ ?_
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (continuous_entry i j)
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (continuous_inv_entry i j)
