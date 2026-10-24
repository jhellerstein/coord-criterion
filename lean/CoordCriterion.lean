-- Foundations (Section 2 definitions, runs)
import CoordCriterion.Foundations.Core
import CoordCriterion.Foundations.Runs
-- §2 Functional CALM, §3 Complete CALM, Appendix B (deferred proofs)
import CoordCriterion.FunctionalCALM.Theorem
import CoordCriterion.CompleteCALM.Theorem
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
import CoordCriterion.CAP.ChosenAvailability
import CoordCriterion.Appendix.DeploymentFor
import CoordCriterion.CAP.ResponseForm
import CoordCriterion.CAP.Register
import CoordCriterion.CAP.ResponseAvailability
import CoordCriterion.CAP.AsyncGilbertLynch
-- §5 Instances (incl. invariant confluence, Appendix B)
import CoordCriterion.Instances.InvariantConfluence
import CoordCriterion.Instances.BailisDefinition
import CoordCriterion.Instances.Examples
-- Figures of §2–§3 and the discussion
import CoordCriterion.Figures
-- Appendix D composition
import CoordCriterion.Appendix.Composition
-- Appendix E deployment
import CoordCriterion.Appendix.Deployment
import CoordCriterion.Appendix.DeploymentExamples
import CoordCriterion.Appendix.DeploymentSystems
-- Appendix G transaction bases
import CoordCriterion.Appendix.TransactionBases.NoReads
import CoordCriterion.Appendix.TransactionBases.Partial
import CoordCriterion.Appendix.TransactionBases.CanonicalExample
-- Appendix H frontiers (Registers covers Appendix E registers and their frontier)
import CoordCriterion.Appendix.Frontiers
import CoordCriterion.Appendix.ProductFrontier
import CoordCriterion.Appendix.Registers
-- Appendix I additional applications
import CoordCriterion.Appendix.Applications
import CoordCriterion.Paper
