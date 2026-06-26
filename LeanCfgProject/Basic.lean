/--
Root import file for the LeanCfgProject package.

This file exists because `LeanCfgProject.lean` imports `LeanCfgProject.Basic`.
For now it imports the MCFG fixed-observation experiment so that ordinary
`lake build` also checks that file.
-/
import LeanCfgProject.MCFG.FI_v2_1_FixedObservation
