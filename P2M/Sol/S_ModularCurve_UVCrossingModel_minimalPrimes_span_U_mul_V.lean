import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isPrime_span_U
import Theorems.Thm_ModularCurve_UVCrossingModel_isPrime_span_V
import Theorems.Thm_ModularCurve_UVCrossingModel_V_notMem_span_U
import Theorems.Thm_ModularCurve_UVCrossingModel_U_notMem_span_V
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_minimalPrimes_span_U_mul_V

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) [IsDomain (W ⧸ Ideal.span {π})] :
    (Ideal.span {U π * V π}).minimalPrimes = {Ideal.span {U π}, Ideal.span {V π}} :=
  by
  have hUprime : (Ideal.span {UVCrossingModel.U π}).IsPrime := ModularCurve.UVCrossingModel.isPrime_span_U π
  have hVprime : (Ideal.span {UVCrossingModel.V π}).IsPrime := ModularCurve.UVCrossingModel.isPrime_span_V π
  have hleU : Ideal.span {UVCrossingModel.U π * UVCrossingModel.V π} ≤
      Ideal.span {UVCrossingModel.U π} :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)))
  have hleV : Ideal.span {UVCrossingModel.U π * UVCrossingModel.V π} ≤
      Ideal.span {UVCrossingModel.V π} :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (Ideal.mem_span_singleton.mpr (dvd_mul_left _ _)))
  have hVU : UVCrossingModel.V π ∉ Ideal.span {UVCrossingModel.U π} := ModularCurve.UVCrossingModel.V_notMem_span_U π
  have hUV : UVCrossingModel.U π ∉ Ideal.span {UVCrossingModel.V π} := ModularCurve.UVCrossingModel.U_notMem_span_V π
  have hmin : ∀ {I P : Ideal (UVCrossingModel W π)}, P ∈ I.minimalPrimes ↔
      (P.IsPrime ∧ I ≤ P) ∧ ∀ Q : Ideal (UVCrossingModel W π), Q.IsPrime ∧ I ≤ Q → Q ≤ P → P ≤ Q :=
    Iff.rfl
  ext P
  rw [hmin]
  constructor
  · rintro ⟨⟨hPprime, hPle⟩, hPmin⟩
    have hmem : UVCrossingModel.U π * UVCrossingModel.V π ∈ P :=
      hPle (Ideal.mem_span_singleton_self _)
    rcases hPprime.mem_or_mem hmem with hU | hV
    · have h1 : Ideal.span {UVCrossingModel.U π} ≤ P :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hU)
      exact Set.mem_insert_iff.mpr (Or.inl (le_antisymm (hPmin _ ⟨hUprime, hleU⟩ h1) h1))
    · have h1 : Ideal.span {UVCrossingModel.V π} ≤ P :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hV)
      refine Set.mem_insert_iff.mpr (Or.inr ?_)
      exact Set.mem_singleton_iff.mpr (le_antisymm (hPmin _ ⟨hVprime, hleV⟩ h1) h1)
  · intro hP
    rcases Set.mem_insert_iff.mp hP with rfl | hP'
    · refine ⟨⟨hUprime, hleU⟩, fun Q hQ hQle => ?_⟩
      rcases hQ.1.mem_or_mem (hQ.2 (Ideal.mem_span_singleton_self _)) with hU | hV
      · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hU)
      · exact absurd (hQle hV) hVU
    · obtain rfl := Set.mem_singleton_iff.mp hP'
      refine ⟨⟨hVprime, hleV⟩, fun Q hQ hQle => ?_⟩
      rcases hQ.1.mem_or_mem (hQ.2 (Ideal.mem_span_singleton_self _)) with hU | hV
      · exact absurd (hQle hU) hUV
      · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hV)
