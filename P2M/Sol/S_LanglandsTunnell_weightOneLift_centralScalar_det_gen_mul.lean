import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Theorems.Thm_LanglandsTunnell_weightOneLift_centralScalar_mul
import P2M.Util
namespace P2MW.S_LanglandsTunnell_weightOneLift_centralScalar_det_gen_mul
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

namespace P2GProbe
namespace C2

open NumberField IsDedekindDomain AutomorphicForm UpperHalfPlane DihedralWeightOne
open scoped ModularForm MatrixGroups

noncomputable section

private theorem det_gen_mem_Z (v : HeightOneSpectrum (𝓞 ℚ)) :
    Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v) ∈ (productionPinsCompact ℚ).Z := by
  rw [productionPinsCompact_Z]
  exact Subgroup.mem_top _

private theorem det_gen_law_of_central_law {n : ℕ} [NeZero n] (f : ℍ → ℂ)
    (χ : DirichletCharacter ℂ n)
    (Φ : HeckeEigensystem ℚ ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Φ.b v = ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ))
    (hlaw : ∀ (z : (productionPinsCompact ℚ).Z) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * g)
        = ((((DirichletCharacter.dirichletIdeleChar χ *
            (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
              (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          (productionPinsCompact ℚ).Z.subtype) z : ℂˣ) : ℂ) * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f
          (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v)) * g)
        = Φ.b v * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  intro v hv g
  rw [hb v hv]
  exact hlaw ⟨Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v), det_gen_mem_Z v⟩ g

end

end P2GProbe.C2

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne in
open IsDedekindDomain in
open scoped ModularForm MatrixGroups in
theorem solution
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
        = Φ.b v * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  exact P2GProbe.C2.det_gen_law_of_central_law f χ Φ S hb
    (LanglandsTunnell.weightOneLift_centralScalar_mul hn f hf χ hχ)
