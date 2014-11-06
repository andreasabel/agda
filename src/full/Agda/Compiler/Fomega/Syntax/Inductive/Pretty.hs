{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverlappingInstances      #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | Pretty printer for Fω syntax

module Agda.Compiler.Fomega.Syntax.Inductive.Pretty where

import Control.Applicative (Applicative)

import Agda.Compiler.Fomega.Syntax
import Agda.Compiler.Fomega.Syntax.Inductive
import Agda.Compiler.Fomega.Syntax.Pretty

import Agda.Utils.NameContext
import Agda.Utils.Pretty

instance (Applicative m, Precedence p, MonadPrec p m) => PrettyM p m Kind where
  prettyPrecM = prettyPrecM . WrapKind

instance (Applicative m, Precedence p, MonadPrec p m, MonadName () m) => PrettyM p m Type where
  prettyPrecM = prettyPrecM . WrapType
