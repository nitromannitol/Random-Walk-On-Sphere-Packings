import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.ENNReal.Real
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Sign
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Disjointed
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Hom.Set
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
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
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Sequences
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.UrysohnsLemma
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
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.TheoremAStatement
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.TheoremBStatement
import SpherePackingsAudit.Vocabulary.BouRabeeGwynne.TilingNetwork
import SpherePackingsAudit.Vocabulary.SpherePackings.Support.Poisson.Basic
import SpherePackingsAudit.Vocabulary.SpherePackings.Support.Voronoi.Basic
import SpherePackingsAudit.Vocabulary.SpherePackings.Support.Voronoi.PoissonCells
import SpherePackingsAudit.Vocabulary.SpherePackings.Support.Voronoi.Tiling

-- VOCABULARY: the declarations of `SpherePackings/Support/Voronoi/PoissonTilings.lean` needed to state the challenges,
-- copied verbatim; generated by `tools/audit/build_vocabulary.py`.

/-!
# Proposition 1.1, second part: Theorems A and B for Poisson–Voronoi tilings

`rw-spheres.tex:371-381` ("In particular, the conclusions of Theorem B and, if `U` is Lipschitz,
Theorem A, hold for the graphs `G_Vor(Λ_m)`") and `rw-spheres.tex:1760-1764`.

Fix a neighbourhood `D = thickening ρ U` of `closure U`.  Almost surely, for all large `m`, the
Voronoi cells of `Λ_m` meeting `D` lie between balls of radii `m^{-8/β⁻}/2` and `m^{-1/(3β⁺)}`, and
every point of `D` is near a point of `Λ_m`; so these cells form an orthogonal tiling of `D`
(`Voronoi.voronoiTiling`).  From such an index `m₀` on, the sequence of these tilings (and before it
the tiling at `m₀`) satisfies the hypotheses of Theorems A and B with hypothesis (II): the mesh is at
most `2 m^{-1/(3β⁺)}`, every nearest vertex is within `m^{-1/(3β⁺)}`, and the smallest tile has
volume at least a constant times `m^{-8d/β⁻}`, which is `exp(-O(log m))`.

The vertices of the tiling are the points of `Λ_m` whose cells meet `D`, rather than all of `Λ_m`;
the Dirichlet problem on `U` and the walk stopped on leaving `U` only involve cells meeting `U`.
-/

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology

namespace SpherePackings

open BouRabeeGwynne Voronoi

variable {d : ℕ}

/-- `T` is the Voronoi tiling of `D` by the point set `S`: its vertices are the points of `S` whose
Voronoi cells meet `D`, and its tiles are those cells. -/
def IsVoronoiTilingOf (T : OrthogonalTiling d) (S D : Set (Euc d)) : Prop :=
  T.domain = D ∧ range T.pos = activePoints S D ∧ ∀ v, (T.cell v).carrier = cell S (T.pos v)

end SpherePackings
