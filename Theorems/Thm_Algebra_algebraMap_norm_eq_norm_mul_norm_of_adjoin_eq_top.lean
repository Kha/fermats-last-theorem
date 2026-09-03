import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top

theorem Algebra.algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top
    {F F₁ F₂ Z Z' : Type*} [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
    [Algebra F F₁] [Algebra F F₂]
    [Algebra F Z] [Algebra F₁ Z] [Algebra F₂ Z] [IsScalarTower F F₁ Z] [IsScalarTower F F₂ Z]
    [Algebra F Z'] [Algebra F₁ Z'] [Algebra F₂ Z'] [IsScalarTower F F₁ Z'] [IsScalarTower F F₂ Z']
    [FiniteDimensional F F₁] [FiniteDimensional F F₂]
    [FiniteDimensional F₁ Z] [FiniteDimensional F₁ Z']
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ Z) ∪ Set.range (algebraMap F₂ Z)) = ⊤)
    (hgen' : Algebra.adjoin F (Set.range (algebraMap F₁ Z') ∪ Set.range (algebraMap F₂ Z')) = ⊤)
    (hdeg : Module.finrank F₁ Z + Module.finrank F₁ Z' = Module.finrank F F₂)
    (hne : ∃ (a : F₂) (b : F₁), algebraMap F₂ Z' a = algebraMap F₁ Z' b ∧
      algebraMap F₂ Z a ≠ algebraMap F₁ Z b)
    (g : F₁) :
    algebraMap F F₂ (Algebra.norm F g)
      = Algebra.norm F₂ (algebraMap F₁ Z g) * Algebra.norm F₂ (algebraMap F₁ Z' g) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top.solution
