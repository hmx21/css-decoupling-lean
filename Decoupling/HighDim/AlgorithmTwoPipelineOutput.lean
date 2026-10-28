import Decoupling.HighDim.DenseCircuitPermutationTheta

/-!
# Uniform runtime output of Algorithm 2

All fields are actual finite data. Native comparison maps, quotient
isomorphisms, and physical correctness belong to proposition proofs and
are not chosen or executed as output data. The two product-state ranks
and the appended identity-check ranks are kept separately.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipeline

structure RuntimeOutput (K : Type*) (D : ℕ) where
  multiplicities : Vector ℕ (D-1)
  species : ℕ
  gates : List (Circuit.Layer K D (Fin species))
  sourceQ : ℕ
  targetQ : ℕ
  sourcePlus : ℕ
  sourceZero : ℕ
  targetPlus : ℕ
  targetZero : ℕ
  sourceIdentityChecks : ℕ
  targetIdentityChecks : ℕ

namespace RuntimeOutput
variable {K : Type*} {D : ℕ}
def sourceAncillas (out : RuntimeOutput K D) : ℕ := out.sourcePlus+out.sourceZero
def targetAncillas (out : RuntimeOutput K D) : ℕ := out.targetPlus+out.targetZero

def empty (K : Type*) (D : ℕ) : RuntimeOutput K D where
  multiplicities := Vector.replicate (D-1) 0
  species := 0
  gates := []
  sourceQ := 0
  targetQ := 0
  sourcePlus := 0
  sourceZero := 0
  targetPlus := 0
  targetZero := 0
  sourceIdentityChecks := 0
  targetIdentityChecks := 0
end RuntimeOutput

end Decoupling.HighDim.AlgorithmTwoPipeline
