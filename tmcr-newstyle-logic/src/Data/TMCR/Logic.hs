{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
module Data.TMCR.Logic where

import qualified Data.Set as Set
import Data.Set (Set(..))
import qualified Data.Map as Map
import Data.Map (Map(..))

import Data.Functor.Foldable
import Data.Functor.Foldable.TH


import Control.Monad.State
import Control.Monad.Reader

import Data.Functor.Classes

import Data.TMCR.ER
import Data.TMCR.Logic.Room


data LogicFile = LogicFile {
            _logicFileEntranceRandoInstructions :: TypedValue Warp WarpTarget,
            _logicFileItemShuffleInstructions :: ItemShuffleInstructions,
            _logicFileRoomConnections :: Set LogicRoom
            } deriving ({-Eq, Ord, -}Show)

data ItemShuffleInstructions = ItemShuffleInstructions
                             deriving (Eq, Ord, Show)
