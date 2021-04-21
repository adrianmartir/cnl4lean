
import CNL4Lean.Grammar
import CNL4Lean.Deserialize

-- This takes way to long to process..
def getChain : DeserializeM Chain := json >>= deserialize
-- This should simply be lowered to IO and then run.

def main : IO Chain := do
  let chain <- getChain.run

-- def getChain' : IO (Except String (Except DeserializationError Chain)) :=
  -- sorry

#eval getChain
