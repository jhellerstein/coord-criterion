-- Foundations (Section 2 definitions, runs)
import CoordCriterion.Foundations.Core
import CoordCriterion.Foundations.Runs
import CoordCriterion.Foundations.IOAutomata
-- §2 Functional CALM, §3 Complete CALM, Appendix B (deferred proofs)
import CoordCriterion.FunctionalCALM.Theorem
import CoordCriterion.CompleteCALM.Theorem
import CoordCriterion.CompleteCALM.Cofinal
import CoordCriterion.CALM.Lemmas
import CoordCriterion.CALM.Examples
import CoordCriterion.CALM.TransientConflict
-- §4.1–4.4 Distributed histories, consistency, systems, coordination; Appendix C
import CoordCriterion.Distributed.Histories
import CoordCriterion.Distributed.Commitments
import CoordCriterion.Distributed.Systems
-- §4.5 Complete CAP; Appendix F (response availability, Gilbert–Lynch)
import CoordCriterion.CAP.Model
import CoordCriterion.CAP.CompleteCAP
import CoordCriterion.CAP.AvailabilityAtEnd
import CoordCriterion.CAP.Necessity
import CoordCriterion.CAP.Forced
import CoordCriterion.CAP.AvailabilityFor
import CoordCriterion.CAP.LocalCommitment
import CoordCriterion.CAP.Coordination
import CoordCriterion.CAP.TwoPhaseCommit
import CoordCriterion.CAP.TimeoutAbort
import CoordCriterion.CAP.ChosenAvailability
import CoordCriterion.Appendix.DeploymentFor
import CoordCriterion.CAP.ResponseForm
import CoordCriterion.CAP.Register
import CoordCriterion.CAP.ResponseAvailability
import CoordCriterion.CAP.AsyncGilbertLynch
-- §6 Instances (incl. invariant confluence, Appendix B)
import CoordCriterion.Instances.InvariantConfluence
import CoordCriterion.Instances.BailisDefinition
import CoordCriterion.Instances.Examples
import CoordCriterion.Instances.QueryRefinements
import CoordCriterion.Instances.StateMachine
import CoordCriterion.Instances.IOMachine
import CoordCriterion.Instances.IOMachineCofinal
import CoordCriterion.Instances.HATRC
import CoordCriterion.Instances.HATSpec
import CoordCriterion.Instances.HATUnion
-- Figures of §2–§3 and the discussion
import CoordCriterion.Figures
-- §5 and Appendix D composition
import CoordCriterion.Appendix.Composition
import CoordCriterion.Appendix.Guarded
import CoordCriterion.Appendix.JointMono
import CoordCriterion.Appendix.Components
import CoordCriterion.Appendix.ComponentSystems
-- Appendix E deployment
import CoordCriterion.Appendix.Deployment
import CoordCriterion.Appendix.DeploymentExamples
import CoordCriterion.Appendix.DeploymentSystems
-- Appendix G transaction bases
import CoordCriterion.Appendix.TransactionBases.NoReads
import CoordCriterion.Appendix.TransactionBases.Spec
import CoordCriterion.Appendix.TransactionBases.Partial
import CoordCriterion.Appendix.TransactionBases.MVTO
import CoordCriterion.Appendix.TransactionBases.CommitEvent
-- Frontier results (not in the paper; kept for future work) and registers (Appendix E)
import CoordCriterion.Appendix.Frontiers
import CoordCriterion.Appendix.ProductFrontier
import CoordCriterion.Appendix.Registers
import CoordCriterion.Appendix.RealTimeCausal
-- Dataflow graphs of stages (not in the paper; exploration)
import CoordCriterion.Appendix.Graphs
-- Appendix H additional applications
import CoordCriterion.Appendix.Applications
import CoordCriterion.Paper
