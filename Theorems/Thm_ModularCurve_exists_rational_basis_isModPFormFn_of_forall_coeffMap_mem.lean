import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_ModPFormFn
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem

set_option autoImplicit false

theorem ModularCurve.exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem
    (L : Type*) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (m : ℕ)
    (V : Submodule L (LaurentSeries L)) [FiniteDimensional L V]
    (hV : ∀ (σ : L ≃ₐ[ℚ] L) (x : LaurentSeries L), x ∈ V → ModularCurve.coeffMap (σ : L →+* L) x ∈ V)
    (hVF : ∀ x ∈ V, x ∈ ModularCurve.laurentBaseChange L F₀)
    (hVB : ∀ x ∈ V, ModularCurve.IsModPFormFn L m x) :
    ∃ (n : ℕ) (Y : Fin n → LaurentSeries ℚ),
      (∀ i, Y i ∈ F₀) ∧ (∀ i, ModularCurve.IsModPFormFn ℚ m (Y i)) ∧ LinearIndependent ℚ Y ∧
      LinearIndependent L (fun i => ModularCurve.coeffEmb L (Y i)) ∧
      Submodule.span L (Set.range fun i => ModularCurve.coeffEmb L (Y i)) = V := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem.solution
