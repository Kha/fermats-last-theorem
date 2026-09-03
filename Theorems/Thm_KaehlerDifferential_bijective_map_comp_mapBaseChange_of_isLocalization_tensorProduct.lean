import Mathlib
import P2M.Util
import P2M.Sol.S_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct

set_option autoImplicit false

universe u

open TensorProduct

theorem KaehlerDifferential.bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct
    (R A A' B C : Type u) [CommRing R] [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    [Algebra R C] [Algebra A C] [Algebra A' C] [Algebra B C]
    [IsScalarTower R A C] [IsScalarTower R B C] [IsScalarTower A A' C] [IsScalarTower R A' C]
    (M : Submonoid A) [IsLocalization M A']
    [Algebra (A ⊗[R] B) C] [IsScalarTower A (A ⊗[R] B) C]
    (hB : (algebraMap (A ⊗[R] B) C).comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C)
    (N : Submonoid (A ⊗[R] B)) [IsLocalization N C] :
    Function.Bijective
      ((KaehlerDifferential.map R A' C C).restrictScalars C ∘ₗ KaehlerDifferential.mapBaseChange R B C) := by p2m_exact_reverting @_root_.P2MW.S_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct.solution
