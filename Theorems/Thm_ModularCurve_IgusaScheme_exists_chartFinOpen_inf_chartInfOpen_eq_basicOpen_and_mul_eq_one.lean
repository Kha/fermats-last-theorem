import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_chartFinOpen_inf_chartInfOpen_eq_basicOpen_and_mul_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_chartFinOpen_inf_chartInfOpen_eq_basicOpen_and_mul_eq_one (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (f : Γ(IgusaScheme N ℓ, chartFinOpen N ℓ)) (g : Γ(IgusaScheme N ℓ, chartInfOpen N ℓ)),
      chartFinOpen N ℓ ⊓ chartInfOpen N ℓ = (IgusaScheme N ℓ).basicOpen f ∧
      chartFinOpen N ℓ ⊓ chartInfOpen N ℓ = (IgusaScheme N ℓ).basicOpen g ∧
      ((IgusaScheme N ℓ).presheaf.map (homOfLE (inf_le_left : chartFinOpen N ℓ ⊓ chartInfOpen N ℓ ≤ chartFinOpen N ℓ)).op).hom f *
        ((IgusaScheme N ℓ).presheaf.map (homOfLE (inf_le_right : chartFinOpen N ℓ ⊓ chartInfOpen N ℓ ≤ chartInfOpen N ℓ)).op).hom g
          = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_chartFinOpen_inf_chartInfOpen_eq_basicOpen_and_mul_eq_one.solution
