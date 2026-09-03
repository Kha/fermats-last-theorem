import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_weightOneLift_centralScalar_det_gen_mul
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne
open IsDedekindDomain
open scoped ModularForm MatrixGroups

theorem LanglandsTunnell.weightOneLift_centralScalar_det_gen_mul
    {n : ℕ} [NeZero n] (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (Φ : HeckeEigensystem ℚ ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Φ.b v = ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ)) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f
          (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v)) * g)
        = Φ.b v * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_weightOneLift_centralScalar_det_gen_mul.solution
