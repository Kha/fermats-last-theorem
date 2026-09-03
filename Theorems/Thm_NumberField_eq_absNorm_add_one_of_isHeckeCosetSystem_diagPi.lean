import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_NumberField_eq_absNorm_add_one_of_isHeckeCosetSystem_diagPi

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.eq_absNorm_add_one_of_isHeckeCosetSystem_diagPi
    (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (ϖ : w.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rT) :
    n = Ideal.absNorm w.asIdeal + 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_eq_absNorm_add_one_of_isHeckeCosetSystem_diagPi.solution
