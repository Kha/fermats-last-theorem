import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import P2M.Util
import P2M.Sol.S_NumberField_NormIndex_IsAdmissibleModulusOfDegree_of_dvd_degree

set_option autoImplicit false

open NumberField NumberField.NormIndex

universe u v

theorem NumberField.NormIndex.IsAdmissibleModulusOfDegree.of_dvd_degree
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [Algebra K L]
    {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) {𝔣 : Ideal (𝓞 K)}
    (h : IsAdmissibleModulusOfDegree K L n 𝔣) : IsAdmissibleModulusOfDegree K L m 𝔣 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_NormIndex_IsAdmissibleModulusOfDegree_of_dvd_degree.solution
