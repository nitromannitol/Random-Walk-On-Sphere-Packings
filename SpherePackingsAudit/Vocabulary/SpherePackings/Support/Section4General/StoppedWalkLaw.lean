import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Sign
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.Approximation
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.CurveSpace
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.DiscretePDE
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.DiscretePDEAlgebra
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.Harmonic
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.LipschitzDomain
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.LocalRegion
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.PaperObjects
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.StoppedCurveLaws
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.StoppedWalk
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.TheoremBStatement
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.TilingNetwork
import SpherePackingsAudit.Vocabulary.SpherePackings.General.MarkovChain.Basic
import SpherePackingsAudit.Vocabulary.SpherePackings.General.MarkovChain.Dirichlet
import SpherePackingsAudit.Vocabulary.SpherePackings.General.NearestNeighbourWalk
import SpherePackingsAudit.Vocabulary.SpherePackings.Support.Section4General.AssumptionD

-- Built on Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne (commit cf73d6e).
-- VOCABULARY: the declarations of `SpherePackings/Support/Section4General/StoppedWalkLaw.lean` needed to state the challenges,
-- copied verbatim; generated by `tools/audit/build_vocabulary.py`.

/-!
# The stopped walk law of Theorem 4.1

For a nearest-neighbour walk on a graph in `ℝ^d` and a set `U`, the law of the walk started at a
vertex `a`, linearly interpolated and stopped at its first exit from `V[U]`, as a law on curves
modulo time parametrization (`rw-spheres.tex:1481-1488`).  On paths that never exit, the stopped
curve is the constant curve at the start (a convention; under Assumption D, for bounded `U` in the
`δ`-neighbourhood of `D`, the walk eventually exits `V[U]` almost surely, `eventually_ae_exit`).
-/

open MeasureTheory Metric Filter Set
open BouRabeeGwynne BouRabeeGwynne.FiniteConductanceNetwork

namespace SpherePackings

variable {d : ℕ}

namespace NearestNeighbourWalk

variable (W : NearestNeighbourWalk d)

/-- The law of the walk from `a`, interpolated and stopped at its first exit from `V[U]`. -/
noncomputable def stoppedWalkLaw (U : Set (Euc d)) (a : W.V) : Measure (CurveSpace d) :=
  (MarkovChain.law W.kernel a).map (stoppedPolygonalCurve (Subtype.val : W.V → Euc d) (W.inner U))

end NearestNeighbourWalk

end SpherePackings
