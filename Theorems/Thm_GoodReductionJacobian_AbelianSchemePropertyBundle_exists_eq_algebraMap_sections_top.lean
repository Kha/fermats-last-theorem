import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_algebraMap_sections_top
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_algebraMap_sections_top
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (𝒦 : A.OrderedAffineCover) (s : Γ(A, ⊤)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
    ∃ c : K, s = algebraMap K Γ(A, ⊤) c := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_algebraMap_sections_top.solution
