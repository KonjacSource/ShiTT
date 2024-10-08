module ShiTT.Termination.Call where 

import ShiTT.Eval
import ShiTT.Context
import ShiTT.Syntax
import Data.Matrix hiding (trace)
import qualified Data.Set as S
import ShiTT.Termination.Ord

instance Ord e => Ord (Matrix e) where 
  compare a b = compare (toList a) (toList b)

data CallMat = CallMat 
  { fromFun :: Fun 
  , callFun :: Fun 
  , callMat :: Matrix Order
  } deriving (Eq, Ord, Show)

-- | The cm function from paper.
-- getCallMat :: (Fun, [Pattern]) -> (Fun, Spine) -> CallMat
-- getCallMat 