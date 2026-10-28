import Decoupling.HighDim.AlgorithmTwoPhysicalTransportIdentityChecks
import Decoupling.HighDim.AlgorithmTwoInvertibleFromPresentation

/-!
# Direct consumer of the actual four-lift program

The comparison datum and both hat matrices come from exactly the same
executed liftMatricesProgram. The returned canonical word is proved to
transport both actual stabilized stabilizer modules. Scalar solvability
is discharged upstream from the actual stable-check beta; no gate list
or comparison identities are accepted as runtime outputs by this wrapper.
-/
namespace Decoupling.HighDim.AlgorithmTwoPhysicalTransport
open Matrix LaurentArithmetic PhysicalIsomorphism AlgorithmTwoInvertible
variable {K : Type*} [Field K] [DecidableEq K] {D c0 c1 t0 t1 zc zt h : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

/-- The actual pipeline word, in its forward C-to-T direction. -/
theorem computed_transports
    (dC : DenseMatrix K D c1 c0 h) (dT : DenseMatrix K D t1 t0 h)
    (F : DenseMatrix K D c1 t1 h) (G : DenseMatrix K D t1 c1 h)
    (hs : FourSolvable (matrixDenote dC) (matrixDenote dT) (matrixDenote F) (matrixDenote G))
    (zC : Matrix (Fin c0) (Fin zc) (Laurent K D))
    (zT : Matrix (Fin t0) (Fin zt) (Laurent K D))
    (hC : ∀ v, matrixDenote dC *ᵥ v = 0 ↔ inImage zC v)
    (hT : ∀ v, matrixDenote dT *ᵥ v = 0 ↔ inImage zT v) :
    let out := (liftMatricesProgram dC dT F G hs).value
    let gates := (DenseCircuitPermutation.canonicalThetaProgram out.psiHat out.phiHat).value
    Transports gates (ordinalIdentification c0 c1 t0 t1)
      (sourceHX (matrixDenote dC)) (targetHX (matrixDenote dT)) (sourceZ zC) (targetZ zT) ∧
    LocalCircuit gates := by
  let out := (liftMatricesProgram dC dT F G hs).value
  let c := comparisonData dC dT F G hs
  refine ⟨?_,actual_localCircuit out.psiHat out.phiHat⟩
  exact transports c zC zT hC hT out.psiHat out.phiHat
    (liftMatricesProgram_psiHat dC dT F G hs) (liftMatricesProgram_phiHat dC dT F G hs)

/-- No choice of a new lift or new circuit intervenes after the actual
augmented presentations and the specified beta representatives. -/
theorem fromPresentations_transports
    {NC NT : Type*} [AddCommGroup NC] [Module (Laurent K D) NC]
    [AddCommGroup NT] [Module (Laurent K D) NT]
    (dC : DenseMatrix K D c1 c0 h) (dT : DenseMatrix K D t1 t0 h)
    (F : DenseMatrix K D c1 t1 h) (G : DenseMatrix K D t1 c1 h)
    (piC : (Fin c1 → Laurent K D) →ₗ[Laurent K D] NC)
    (piT : (Fin t1 → Laurent K D) →ₗ[Laurent K D] NT)
    (exactC : LinearMap.range (matrixDenote dC).mulVecLin = LinearMap.ker piC)
    (exactT : LinearMap.range (matrixDenote dT).mulVecLin = LinearMap.ker piT)
    (beta : NT ≃ₗ[Laurent K D] NC)
    (hF : piC.comp (matrixDenote F).mulVecLin = beta.toLinearMap.comp piT)
    (hG : piT.comp (matrixDenote G).mulVecLin = beta.symm.toLinearMap.comp piC)
    (zC : Matrix (Fin c0) (Fin zc) (Laurent K D))
    (zT : Matrix (Fin t0) (Fin zt) (Laurent K D))
    (hC : ∀ v, matrixDenote dC *ᵥ v = 0 ↔ inImage zC v)
    (hT : ∀ v, matrixDenote dT *ᵥ v = 0 ↔ inImage zT v) :
    let out := (fromPresentationsProgram dC dT F G piC piT exactC exactT beta hF hG).value
    let gates := (DenseCircuitPermutation.canonicalThetaProgram out.psiHat out.phiHat).value
    Transports gates (ordinalIdentification c0 c1 t0 t1)
      (sourceHX (matrixDenote dC)) (targetHX (matrixDenote dT)) (sourceZ zC) (targetZ zT) ∧
    LocalCircuit gates :=
  computed_transports dC dT F G
    (solvableOfPresentations dC dT F G piC piT exactC exactT beta hF hG) zC zT hC hT

end
end Decoupling.HighDim.AlgorithmTwoPhysicalTransport
