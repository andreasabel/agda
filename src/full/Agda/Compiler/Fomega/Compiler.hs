-- | Entry point module for type-directed compilation.

module Agda.Compiler.Fomega.Compiler where

import Agda.TypeChecking.Monad

compilerMain :: Interface -> TCM ()
compilerMain i = do
  return ()
  -- forM (HashMap.toList $ iSignature i) $ \ (q, def) -> do
  --   pretty (q, extractType (defType def))
