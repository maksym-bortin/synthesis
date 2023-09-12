This repository contains the material accompanying the publication
'Structured development of implementations for divide-and-conquer specifications'[https://doi.org/10.1016/j.scico.2023.103011],
and comprises the following theories for the Isabelle/HOL theorem prover 
(versions 2023 and 2022, see www.cl.cam.ac.uk/research/hvg/Isabelle and LICENSE for details):

 - Preliminaries.thy  -- the underlying framework
 - DaC_synthesis.thy  -- the divide-and-conquer design tactic with the relator used in the publication
 - Powerset.thy       -- an introductory example application of the tactic to power set construction
 - Greedy.thy         -- the case study concerning bases of finite matroids
 - Scheduling.thy     -- an application of the greedy tactic to a scheduling problem
 - DaC_synthesis2.thy -- the same divide-and-conquer tactic but with another relator          
 - Quicksort.thy      -- an application of the tactic resulting in a quicksort algorithm.



