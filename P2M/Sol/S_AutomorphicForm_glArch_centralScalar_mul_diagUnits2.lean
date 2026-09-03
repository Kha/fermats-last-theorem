import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
namespace P2MW.S_AutomorphicForm_glArch_centralScalar_mul_diagUnits2

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem solution
    (K : Type) [Field K] [NumberField K] (z a b : (AdeleRing (𝓞 K) K)ˣ) :
    AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 a b) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) z) *
        diagUnits2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) a)
          (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) b)  := by
  rw [map_mul]
  congr 1
  · apply Units.ext; ext i j
    rw [AdelicLevel.glArch_apply]
    change (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) i j).1 =
      Matrix.scalar (Fin 2) ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) z :
        (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) i j
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs <;> rfl
  · apply Units.ext; ext i j
    rw [AdelicLevel.glArch_apply]
    change ((!![(a : AdeleRing (𝓞 K) K), 0; 0, (b : AdeleRing (𝓞 K) K)] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 =
      (!![((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) a : (InfiniteAdeleRing K)ˣ) :
          InfiniteAdeleRing K), 0; 0,
        ((Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) b : (InfiniteAdeleRing K)ˣ) :
          InfiniteAdeleRing K)] : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j
    fin_cases i <;> fin_cases j <;> rfl
