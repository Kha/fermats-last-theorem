import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
namespace P2MW.S_AdelicDock_finEmbed_localEmbed_comm_of_ne

set_option autoImplicit false

open IsDedekindDomain AdelicDock

theorem solution {R : Type*} {K : Type*} [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {v w : HeightOneSpectrum R} (hvw : v ≠ w)
    (x : GL (Fin 2) (v.adicCompletion K)) (y : GL (Fin 2) (w.adicCompletion K)) :
    finEmbed R K (localEmbed R K v x) * finEmbed R K (localEmbed R K w y) =
      finEmbed R K (localEmbed R K w y) * finEmbed R K (localEmbed R K v x) := by
  rw [← map_mul (finEmbed R K), ← map_mul (finEmbed R K)]
  congr 1
  refine Units.ext ?_
  simp only [Units.val_mul, coe_localEmbed]
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun u => ?_
  rw [map_mul, map_mul]
  by_cases huv : u = v
  · subst huv
    rw [mapMatrix_localMat_self, mapMatrix_localMat_of_ne R K w _ hvw, mul_one, one_mul]
  · by_cases huw : u = w
    · subst huw
      rw [mapMatrix_localMat_self, mapMatrix_localMat_of_ne R K v _ huv, mul_one, one_mul]
    · rw [mapMatrix_localMat_of_ne R K v _ huv, mapMatrix_localMat_of_ne R K w _ huw]
