module ShiTT.Termination.Check where 

import ShiTT.Termination.Call
import ShiTT.Context

-- | The given context should contain the fake definitions (which means only fun header) of mutual functions.
checkTermination :: Context -> MutualSet -> Bool
checkTermination ctx mut = decreasing (complete (initCallSet ctx mut))