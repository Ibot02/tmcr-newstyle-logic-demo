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
module Data.TMCR.ER where

import qualified Data.Set as Set
import Data.Set (Set(..))
import qualified Data.Map as Map
import Data.Map (Map(..))

import Data.Functor.Foldable
import Data.Functor.Foldable.TH

import System.Random

import Control.Monad.State
import Control.Monad.Reader

import Data.Functor.Classes

data ERType = Unit | Atom | Door | Warp | WarpTarget
            deriving (Eq, Ord, Show, Enum)

data ERTypeWitness a where
        UnitW :: ERTypeWitness Unit
        AtomW :: ERTypeWitness Atom
        DoorW :: ERTypeWitness Door
        WarpW :: ERTypeWitness Warp
        WarpTargetW :: ERTypeWitness WarpTarget

deriving instance Eq (ERTypeWitness a)
deriving instance Ord (ERTypeWitness a)
deriving instance Show (ERTypeWitness a)

data (a :: k) :~: (b :: k) where
    Refl :: a :~: a

checkEq :: ERTypeWitness a -> ERTypeWitness b -> Maybe (a :~: b)
checkEq UnitW UnitW = Just Refl
checkEq AtomW AtomW = Just Refl
checkEq DoorW DoorW = Just Refl
checkEq WarpW WarpW = Just Refl
checkEq WarpTargetW WarpTargetW = Just Refl
checkEq _ _ = Nothing

data ConstantID = All | Tagged String | Named String
                deriving (Eq, Ord, Show)

data PreTypecheckValue = PTCVanilla
                       | PTCDoorWarp
                       | PTCDoorTarget
                       | PTCConstantWarp ConstantID
                       | PTCConstantTarget ConstantID
                       | PTCConstantDoor ConstantID
                       | PTCGivenFlag String
                       | PTCGivenDropdown String
                       | PTCAtomSet (Set String)
                       | PTCIdentity
                       | PTCEmpty
                       | PTCCompose PreTypecheckValue PreTypecheckValue
                       | PTCUnion PreTypecheckValue PreTypecheckValue
                       | PTCIntersection PreTypecheckValue PreTypecheckValue
                       | PTCDifference PreTypecheckValue PreTypecheckValue
                       | PTCLeftUnion PreTypecheckValue PreTypecheckValue --Union but the second argument is restricted to keys that don't occur in the first
                       | PTCReverse PreTypecheckValue
                       | PTCITE PreTypecheckValue PreTypecheckValue PreTypecheckValue
                       | PTCRandomEnsureFunction Bool PreTypecheckValue --randomly restrict to ensure it is a function and injective if the given bool is true
                       | PTCRandomSymmetric Bool PreTypecheckValue --randomly restrict to ensure symmetry. If the bool is true and when acting on doors, minimize the number of components of the result (when considering doors in the same room to be connected)?
                        deriving (Eq, Ord, Show)
--random restrictions shall ensure the result is of maximal cardinality

$(makeBaseFunctor ''PreTypecheckValue)

deriving instance (Eq a) => Eq (PreTypecheckValueF a)
deriving instance (Ord a) => Ord (PreTypecheckValueF a)
deriving instance (Show a) => Show (PreTypecheckValueF a)

instance Eq1 PreTypecheckValueF where
    liftEq f x y = liftCompare (\a b -> if f a b then EQ else LT) x y == EQ
instance Ord1 PreTypecheckValueF where
    liftCompare _ PTCVanillaF PTCVanillaF = EQ
    liftCompare _ PTCVanillaF _ = LT
    liftCompare _ _ PTCVanillaF = GT
    liftCompare _ PTCDoorWarpF PTCDoorWarpF = EQ
    liftCompare _ PTCDoorWarpF _ = LT
    liftCompare _ _ PTCDoorWarpF = GT
    liftCompare _ PTCDoorTargetF PTCDoorTargetF = EQ
    liftCompare _ PTCDoorTargetF _ = LT
    liftCompare _ _ PTCDoorTargetF = GT
    liftCompare _ (PTCConstantWarpF w) (PTCConstantWarpF w') = compare w w'
    liftCompare _ (PTCConstantWarpF _) _ = LT
    liftCompare _ _ (PTCConstantWarpF _) = GT
    liftCompare _ (PTCConstantTargetF w) (PTCConstantTargetF w') = compare w w'
    liftCompare _ (PTCConstantTargetF _) _ = LT
    liftCompare _ _ (PTCConstantTargetF _) = GT
    liftCompare _ (PTCConstantDoorF w) (PTCConstantDoorF w') = compare w w'
    liftCompare _ (PTCConstantDoorF _) _ = LT
    liftCompare _ _ (PTCConstantDoorF _) = GT
    liftCompare _ (PTCGivenFlagF s) (PTCGivenFlagF s') = compare s s'
    liftCompare _ (PTCGivenFlagF _) _ = LT
    liftCompare _ _ (PTCGivenFlagF _) = GT
    liftCompare _ (PTCGivenDropdownF s) (PTCGivenDropdownF s') = compare s s'
    liftCompare _ (PTCGivenDropdownF _) _ = LT
    liftCompare _ _ (PTCGivenDropdownF _) = GT
    liftCompare _ (PTCAtomSetF s) (PTCAtomSetF s') = compare s s'
    liftCompare _ (PTCAtomSetF _) _ = LT
    liftCompare _ _ (PTCAtomSetF _) = GT
    liftCompare _ PTCIdentityF PTCIdentityF = EQ
    liftCompare _ PTCIdentityF _ = LT
    liftCompare _ _ PTCIdentityF = GT
    liftCompare _ PTCEmptyF PTCEmptyF = EQ
    liftCompare _ PTCEmptyF _ = LT
    liftCompare _ _ PTCEmptyF = GT
    liftCompare f (PTCComposeF x1 x2) (PTCComposeF x1' x2') = f x1 x1' <> f x2 x2'
    liftCompare _ (PTCComposeF _ _) _ = LT
    liftCompare _ _ (PTCComposeF _ _) = GT
    liftCompare f (PTCUnionF x1 x2) (PTCUnionF x1' x2') = f x1 x1' <> f x2 x2'
    liftCompare _ (PTCUnionF _ _) _ = LT
    liftCompare _ _ (PTCUnionF _ _) = GT
    liftCompare f (PTCIntersectionF x1 x2) (PTCIntersectionF x1' x2') = f x1 x1' <> f x2 x2'
    liftCompare _ (PTCIntersectionF _ _) _ = LT
    liftCompare _ _ (PTCIntersectionF _ _) = GT
    liftCompare f (PTCDifferenceF x1 x2) (PTCDifferenceF x1' x2') = f x1 x1' <> f x2 x2'
    liftCompare _ (PTCDifferenceF _ _) _ = LT
    liftCompare _ _ (PTCDifferenceF _ _) = GT
    liftCompare f (PTCLeftUnionF x1 x2) (PTCLeftUnionF x1' x2') = f x1 x1' <> f x2 x2'
    liftCompare _ (PTCLeftUnionF _ _) _ = LT
    liftCompare _ _ (PTCLeftUnionF _ _) = GT
    liftCompare f (PTCReverseF x1) (PTCReverseF x1') = f x1 x1'
    liftCompare _ (PTCReverseF _) _ = LT
    liftCompare _ _ (PTCReverseF _) = GT
    liftCompare f (PTCITEF x1 x2 x3) (PTCITEF x1' x2' x3') = f x1 x1' <> f x2 x2' <> f x3 x3'
    liftCompare _ (PTCITEF _ _ _) _ = LT
    liftCompare _ _ (PTCITEF _ _ _) = GT
    liftCompare f (PTCRandomEnsureFunctionF b x1) (PTCRandomEnsureFunctionF b' x1') = compare b b' <> f x1 x1'
    liftCompare _ (PTCRandomEnsureFunctionF _ _) _ = LT
    liftCompare _ _ (PTCRandomEnsureFunctionF _ _) = GT
    liftCompare f (PTCRandomSymmetricF b x1) (PTCRandomSymmetricF b' x1') = compare b b' <> f x1 x1'
    liftCompare _ (PTCRandomSymmetricF _ _) _ = LT
    liftCompare _ _ (PTCRandomSymmetricF _ _) = GT


data TypedValue (a :: ERType) (b :: ERType) where
                Vanilla :: TypedValue Warp WarpTarget
                DoorWarp :: TypedValue Door Warp
                DoorTarget :: TypedValue Door WarpTarget
                ConstantWarp :: ConstantID -> TypedValue Warp Unit
                ConstantTarget :: ConstantID -> TypedValue WarpTarget Unit
                ConstantDoor :: ConstantID -> TypedValue Door Unit
                GivenFlag :: String -> TypedValue Unit Unit
                GivenDropdown :: String -> TypedValue Unit Atom
                AtomSet :: Set String -> TypedValue Atom Unit
                Identity :: ERTypeWitness a -> TypedValue a a
                Empty :: ERTypeWitness a -> TypedValue a a
                Compose :: TypedValue a b -> TypedValue b c -> TypedValue a c
                Union :: TypedValue a b -> TypedValue a b -> TypedValue a b
                Intersection :: TypedValue a b -> TypedValue a b -> TypedValue a b
                Difference :: TypedValue a b -> TypedValue a b -> TypedValue a b
                LeftUnion :: TypedValue a b -> TypedValue a b -> TypedValue a b
                Reverse :: TypedValue b a -> TypedValue a b
                ITE :: TypedValue Unit Unit -> TypedValue a b -> TypedValue a b -> TypedValue a b
                RandomEnsureFunction :: Bool -> TypedValue a b -> TypedValue a b
                RandomSymmetric :: Bool -> TypedValue a a -> TypedValue a a

-- deriving instance Eq (TypedValue a b)
-- deriving instance Ord (TypedValue a b)
deriving instance Show (TypedValue a b)

forgetTypes :: TypedValue a b -> PreTypecheckValue
forgetTypes Vanilla = PTCVanilla
forgetTypes DoorWarp = PTCDoorWarp
forgetTypes DoorTarget = PTCDoorTarget
forgetTypes (ConstantWarp s) = PTCConstantWarp s
forgetTypes (ConstantTarget s) = PTCConstantTarget s
forgetTypes (ConstantDoor s) = PTCConstantDoor s
forgetTypes (GivenFlag s) = PTCGivenFlag s
forgetTypes (GivenDropdown s) = PTCGivenDropdown s
forgetTypes (AtomSet s) = PTCAtomSet s
forgetTypes (Identity _) = PTCIdentity
forgetTypes (Empty _) = PTCEmpty
forgetTypes (Compose a b) = PTCCompose (forgetTypes a) (forgetTypes b)
forgetTypes (Union a b) = PTCUnion (forgetTypes a) (forgetTypes b)
forgetTypes (Intersection a b) = PTCIntersection (forgetTypes a) (forgetTypes b)
forgetTypes (LeftUnion a b) = PTCLeftUnion (forgetTypes a) (forgetTypes b)
forgetTypes (Difference a b) = PTCDifference (forgetTypes a) (forgetTypes b)
forgetTypes (Reverse a) = PTCReverse (forgetTypes a)
forgetTypes (ITE a b c) = PTCITE (forgetTypes a) (forgetTypes b) (forgetTypes c)
forgetTypes (RandomEnsureFunction b a) = PTCRandomEnsureFunction b (forgetTypes a)
forgetTypes (RandomSymmetric b a) = PTCRandomSymmetric b (forgetTypes a)

data TypeError = Mismatch
               deriving (Eq, Ord, Show)

data TypeContext e v = TypeContext 
                       { runTypeContextBothKnown :: forall a b. ERTypeWitness a -> ERTypeWitness b -> Either e (v a b)
                       , runTypeContextLeftToRight :: forall a c. ERTypeWitness a -> (forall b. (v a b, ERTypeWitness b) -> c) -> Either e c
                       , runTypeContextRightToLeft :: forall b c. ERTypeWitness b -> (forall a. (ERTypeWitness a, v a b) -> c) -> Either e c
                       }

ensure :: ERTypeWitness a -> ERTypeWitness b -> e -> v a b -> TypeContext e v
ensure a b e v = TypeContext {
                  runTypeContextBothKnown = \a' b' -> case (checkEq a a', checkEq b b') of
                    (Just Refl, Just Refl) -> Right v
                    _ -> Left e
                , runTypeContextLeftToRight = \a' c -> case checkEq a a' of
                    Just Refl -> Right $ c (v,b)
                    Nothing -> Left e
                , runTypeContextRightToLeft = \b' c -> case checkEq b b' of
                    Just Refl -> Right $ c (a,v)
                    Nothing -> Left e
                }
ensureEndo :: (forall a b. ERTypeWitness a -> ERTypeWitness b -> e) -> (forall a. ERTypeWitness a -> v a a) -> TypeContext e v
ensureEndo e f = TypeContext
                    { runTypeContextBothKnown = \a b -> case checkEq a b of
                            Just Refl -> Right $ f a
                            Nothing -> Left $ e a b
                    , runTypeContextLeftToRight = \a c -> Right $ c (f a, a)
                    , runTypeContextRightToLeft = \a c -> Right $ c (a, f a)
                    }
ensureSame :: (forall a b. v a b -> v' a b -> v'' a b) -> TypeContext e v -> TypeContext e v' -> TypeContext e v''
ensureSame c f g = TypeContext
                    { runTypeContextBothKnown = \a b -> do
                        v1 <- runTypeContextBothKnown f a b
                        v2 <- runTypeContextBothKnown g a b
                        return $ c v1 v2
                    , runTypeContextLeftToRight = \a h -> join $ runTypeContextLeftToRight f a (\(v1, b) -> case runTypeContextBothKnown g a b of
                        Left e -> Left e
                        Right v2 -> Right $ h (c v1 v2, b))
                    , runTypeContextRightToLeft = \b h -> join $ runTypeContextRightToLeft f b (\(a, v1) -> case runTypeContextBothKnown g a b of
                        Left e -> Left e
                        Right v2 -> Right $ h (a, c v1 v2))
                    }

mapContext :: (forall a b. v a b -> v' a b) -> TypeContext e v -> TypeContext e v'
mapContext f v = TypeContext
                    { runTypeContextBothKnown = \a b -> fmap f $ runTypeContextBothKnown v a b
                    , runTypeContextLeftToRight = \a c -> runTypeContextLeftToRight v a (\(v', b) -> c (f v', b))
                    , runTypeContextRightToLeft = \b c -> runTypeContextRightToLeft v b (\(a, v') -> c (a, f v'))
                    }

alwaysFail :: e -> TypeContext e v
alwaysFail e = TypeContext
                { runTypeContextBothKnown = \_ _ -> Left e
                , runTypeContextLeftToRight = \_ _ -> Left e
                , runTypeContextRightToLeft = \_ _ -> Left e
                }

typing :: PreTypecheckValueF (TypeContext TypeError TypedValue) -> TypeContext TypeError TypedValue
typing PTCVanillaF = ensure WarpW WarpTargetW Mismatch Vanilla
typing PTCDoorWarpF = ensure DoorW WarpW Mismatch DoorWarp
typing PTCDoorTargetF = ensure DoorW WarpTargetW Mismatch DoorTarget
typing (PTCConstantWarpF s) = ensure WarpW UnitW Mismatch $ ConstantWarp s
typing (PTCConstantTargetF s) = ensure WarpTargetW UnitW Mismatch $ ConstantTarget s
typing (PTCConstantDoorF s) = ensure DoorW UnitW Mismatch $ ConstantDoor s
typing (PTCGivenFlagF s) = ensure UnitW UnitW Mismatch $ GivenFlag s
typing (PTCGivenDropdownF s) = ensure UnitW AtomW Mismatch $ GivenDropdown s
typing (PTCAtomSetF s) = ensure AtomW UnitW Mismatch $ AtomSet s
typing PTCIdentityF = ensureEndo (\_ _ -> Mismatch) Identity
typing PTCEmptyF = ensureEndo (\_ _ -> Mismatch) Empty
typing (PTCComposeF ctxX ctxY) = TypeContext {
                          runTypeContextBothKnown = \a c -> join $ runTypeContextLeftToRight ctxX a $ \(x, b) -> fmap (Compose x) $ runTypeContextBothKnown ctxY b c
                        , runTypeContextLeftToRight = \a f -> join $ runTypeContextLeftToRight ctxX a $ \(x, b) -> runTypeContextLeftToRight ctxY b $ \(y, c) -> f (Compose x y, c)
                        , runTypeContextRightToLeft = \c f -> join $ runTypeContextRightToLeft ctxY c $ \(b, y) -> runTypeContextRightToLeft ctxX b $ \(a, x) -> f (a, Compose x y)
                        }
typing (PTCUnionF ctxa ctxb) = ensureSame Union ctxa ctxb
typing (PTCIntersectionF ctxa ctxb) = ensureSame Intersection ctxa ctxb
typing (PTCLeftUnionF ctxa ctxb) = ensureSame LeftUnion ctxa ctxb
typing (PTCDifferenceF ctxa ctxb) = ensureSame Difference ctxa ctxb
typing (PTCReverseF ctx) = TypeContext 
                        { runTypeContextBothKnown = \a b -> Reverse <$> runTypeContextBothKnown ctx b a
                        , runTypeContextLeftToRight = \a f -> runTypeContextRightToLeft ctx a (\(b, v) -> f (Reverse v, b))
                        , runTypeContextRightToLeft = \b f -> runTypeContextLeftToRight ctx b (\(v, a) -> f (a, Reverse v))
                        }
typing (PTCITEF ctxa ctxb ctxc) = case runTypeContextBothKnown ctxa UnitW UnitW of
                                    Left e -> alwaysFail e
                                    Right v -> ensureSame (ITE v) ctxb ctxc
typing (PTCRandomEnsureFunctionF a ctx) = mapContext (RandomEnsureFunction a) ctx
typing (PTCRandomSymmetricF x ctx) = TypeContext
            { runTypeContextBothKnown = \a b -> case checkEq a b of
                Nothing -> Left Mismatch
                Just Refl -> fmap (RandomSymmetric x) $ runTypeContextBothKnown ctx a b
            , runTypeContextLeftToRight = \a f -> fmap (\y -> f (RandomSymmetric x y,a)) $ runTypeContextBothKnown ctx a a
            , runTypeContextRightToLeft = \a f -> fmap (\y -> f (a, RandomSymmetric x y)) $ runTypeContextBothKnown ctx a a
            }

data PTCBaseCase = BaseCaseVanilla
                 | BaseCaseDoorWarp
                 | BaseCaseDoorTarget
                 | BaseCaseConstantWarp ConstantID
                 | BaseCaseConstantTarget ConstantID
                 | BaseCaseConstantDoor ConstantID
                 | BaseCaseFlag String
                 | BaseCaseDropdown String
                 | BaseCaseAtoms (Set String)
                 | BaseCaseIdentity
                 | BaseCaseEmpty

withCombine :: (a -> a -> a) -> (PTCBaseCase -> a) -> PreTypecheckValueF a -> a
withCombine c b PTCVanillaF = b BaseCaseVanilla
withCombine c b PTCDoorWarpF = b BaseCaseDoorWarp
withCombine c b PTCDoorTargetF = b BaseCaseDoorTarget
withCombine c b (PTCConstantWarpF s) = b $ BaseCaseConstantWarp s
withCombine c b (PTCConstantTargetF s) = b $ BaseCaseConstantTarget s
withCombine c b (PTCConstantDoorF s) = b $ BaseCaseConstantDoor s
withCombine c b (PTCGivenFlagF s) = b $ BaseCaseFlag s
withCombine c b (PTCGivenDropdownF s) = b $ BaseCaseDropdown s
withCombine c b (PTCAtomSetF s) = b $ BaseCaseAtoms s
withCombine c b (PTCIdentityF) = b $ BaseCaseIdentity
withCombine c b (PTCEmptyF) = b $ BaseCaseEmpty
withCombine c b (PTCComposeF x y) = c x y
withCombine c b (PTCUnionF x y) = c x y
withCombine c b (PTCIntersectionF x y) = c x y
withCombine c b (PTCLeftUnionF x y) = c x y
withCombine c b (PTCDifferenceF x y) = c x y
withCombine c b (PTCReverseF x) = x
withCombine c b (PTCITEF x y z) = c x $ c y z
withCombine c b (PTCRandomEnsureFunctionF _ x) = x
withCombine c b (PTCRandomSymmetricF _ x) = x

collectAtoms :: PreTypecheckValueF (Set String) -> Set String
collectAtoms = withCombine (Set.union) $ \case
                    BaseCaseAtoms a -> a
                    _ -> Set.empty

testTermValid :: PreTypecheckValue
testTermValid = PTCITE (PTCGivenFlag "EntranceRando") (PTCRandomEnsureFunction False (PTCCompose (PTCConstantWarp (All)) (PTCCompose (PTCReverse (PTCConstantWarp All)) PTCVanilla))) PTCVanilla

testTermInvalid :: PreTypecheckValue
testTermInvalid = PTCITE (PTCGivenFlag "EntranceRando") (PTCCompose (PTCConstantWarp (Tagged "Shuffleable")) (PTCCompose (PTCConstantWarp (Tagged "Shuffleable")) PTCVanilla)) PTCVanilla

data DoorData = DoorData {
        doorName1 :: String,
        doorName2 :: String,
        doorRoom1 :: String,
        doorRoom2 :: String
        } --represents a vanilla door between room1 and room2, where the side in room1 is named name1 and the side in room2 is named name2
        deriving (Eq, Ord, Show)

data WarpData = WarpData {
        warpName :: String,
        warpSourceRoom :: String,
        warpTargetRoom :: String
        }
        deriving (Eq, Ord, Show)

data WarpID = WarpName String | WarpDoorName String
        deriving (Eq, Ord, Show)

data WarpTargetID = WarpTargetName String | WarpTargetDoorName String
        deriving (Eq, Ord, Show)

typecheck :: PreTypecheckValue -> Either TypeError (TypedValue Warp WarpTarget)
typecheck v = runTypeContextBothKnown (cata typing v) WarpW WarpTargetW

data ExtraData = ExtraData {
                doors :: Set DoorData,
                oneWayWarps :: Set WarpData,
                flags :: Map String Bool,
                dropdowns :: Map String String
                } deriving (Eq, Ord, Show)

data Rep a where
    WarpRep :: WarpID -> Rep Warp
    WarpTargetRep :: WarpTargetID -> Rep WarpTarget
    DoorRep :: String -> Rep Door
    UnitRep :: Rep Unit
    AtomRep :: String -> Rep Atom

deriving instance Show (Rep a)
deriving instance Eq (Rep a)
deriving instance Ord (Rep a)

everything :: (MonadReader (ExtraData, Set String) m) => ERTypeWitness a -> m (Set (Rep a))
everything WarpW = fmap (\e -> Set.map WarpRep (Set.map (WarpDoorName . doorName1) (doors e) <> Set.map (WarpDoorName . doorName2) (doors e) <> Set.map (WarpName . warpName) (oneWayWarps e))) $ asks fst
everything WarpTargetW = fmap (\e -> Set.map WarpTargetRep (Set.map (WarpTargetDoorName . doorName1) (doors e) <> Set.map (WarpTargetDoorName . doorName2) (doors e) <> Set.map (WarpTargetName . warpName) (oneWayWarps e))) $ asks fst
everything DoorW = fmap (\e -> Set.map (DoorRep . doorName1) (doors e) <> Set.map (DoorRep . doorName2) (doors e)) $ asks fst
everything UnitW = return $ Set.singleton UnitRep
everything AtomW = Set.map AtomRep <$> asks snd

toSetRep :: Set a -> (Set (a,Rep Unit), Set (Rep Unit, a))
toSetRep s = (Set.mapMonotonic (\x -> (x,UnitRep)) s, Set.mapMonotonic (\x -> (UnitRep,x)) s)

identityOf :: Set a -> (Set (a,a), Set (a,a))
identityOf s = (Set.mapMonotonic (\x -> (x,x)) s, Set.mapMonotonic (\x -> (x,x)) s)

collectMatching :: (Ord a, Ord b, Ord c) => Set (a,b) -> Set (a,c) -> (Set (b,c), Set (c,b))
collectMatching x y = helper (Set.toAscList x) (Set.toAscList y) (Set.empty, Set.empty) where
        helper [] _ r = r
        helper _ [] r = r
        helper l@((a,_):_) l'@((a',_):_) r = case compare a a' of
            LT -> helper (dropWhile ((< a') . fst) l) l' r
            GT -> helper l (dropWhile ((a >) . fst) l') r
            EQ -> let (lx, lr) = span ((a ==) . fst) l; (lx', lr') = span ((== a') . fst) l' in helper lr lr' $ insertPairs (snd <$> lx) (snd <$> lx') r
        insertPairs :: (Ord a, Ord b) => [a] -> [b] -> (Set (a,b), Set (b,a)) -> (Set (a,b), Set (b,a))
        insertPairs (Set.fromList -> a) (Set.fromList -> b) (r, r') = (r <> Set.cartesianProduct a b, r' <> Set.cartesianProduct b a)

eval :: (MonadState g m, RandomGen g) => ExtraData -> TypedValue a b -> m (Set (Rep a, Rep b))
eval extras value = flip runReaderT (extras, Set.fromList (Map.elems (dropdowns extras)) <> cata collectAtoms (forgetTypes value)) $ fmap fst $ eval' value where
            eval' :: (MonadState g m, RandomGen g) => TypedValue a b -> ReaderT (ExtraData, Set String) m (Set (Rep a, Rep b), Set (Rep b, Rep a))
            eval' Vanilla = do
                ex <- asks fst
                let v = Set.map (\w -> (WarpRep $ WarpName $ warpName w, WarpTargetRep $ WarpTargetName $ warpName w)) (oneWayWarps ex)
                     <> Set.map (\w -> (WarpRep $ WarpDoorName $ doorName1 w, WarpTargetRep $ WarpTargetDoorName $ doorName2 w)) (doors ex)
                     <> Set.map (\w -> (WarpRep $ WarpDoorName $ doorName2 w, WarpTargetRep $ WarpTargetDoorName $ doorName1 w)) (doors ex)
                return (v, Set.map (\(a,b) -> (b,a)) v)
            eval' DoorWarp = do
                d <- everything DoorW
                let d'  = Set.mapMonotonic (\r@(DoorRep name) -> (r, WarpRep $ WarpDoorName name)) d
                    d'' = Set.mapMonotonic (\r@(DoorRep name) -> (WarpRep $ WarpDoorName name, r)) d
                return (d', d'')
            eval' DoorTarget = do
                d <- everything DoorW
                let d'  = Set.mapMonotonic (\r@(DoorRep name) -> (r, WarpTargetRep $ WarpTargetDoorName name)) d
                    d'' = Set.mapMonotonic (\r@(DoorRep name) -> (WarpTargetRep $ WarpTargetDoorName name, r)) d
                return (d', d'')
            eval' (ConstantWarp All) = fmap toSetRep $ everything WarpW
            eval' (ConstantTarget All) = fmap toSetRep $ everything WarpTargetW
            eval' (ConstantDoor All) = fmap toSetRep $ everything DoorW
            eval' (ConstantWarp (Named s)) = fmap (toSetRep . Set.intersection (Set.singleton $ WarpRep $ WarpName $ s)) $ everything WarpW
            eval' (ConstantTarget (Named s)) = fmap (toSetRep . Set.intersection (Set.singleton $ WarpTargetRep $ WarpTargetName $ s)) $ everything WarpTargetW
            eval' (ConstantDoor (Named s)) = fmap (toSetRep . Set.intersection (Set.singleton $ DoorRep $ s)) $ everything DoorW
            eval' (ConstantWarp (Tagged s)) = return (Set.empty, Set.empty)
            eval' (ConstantTarget (Tagged s)) = return (Set.empty, Set.empty)
            eval' (ConstantDoor (Tagged s)) = return (Set.empty, Set.empty)
            --todo tags
            eval' (GivenFlag s) = do
                ex <- asks fst
                let b = Map.findWithDefault False s $ flags ex
                    true = Set.singleton (UnitRep, UnitRep)
                return $ if b then (true, true) else (Set.empty, Set.empty)
            eval' (GivenDropdown s) = do
                ex <- asks fst
                case Map.lookup s (dropdowns ex) of
                    Nothing -> return (Set.empty, Set.empty)
                    Just v -> return (Set.singleton (UnitRep, AtomRep v), Set.singleton (AtomRep v, UnitRep))
            eval' (AtomSet s) = return $ toSetRep $ Set.mapMonotonic AtomRep s
            eval' (Identity w) = identityOf <$> everything w
            eval' (Empty w) = return $ (Set.empty, Set.empty)
            eval' (Compose x1 x2) = do
                (_, r1) <- eval' x1
                (r2, _) <- eval' x2
                return $ collectMatching r1 r2
            eval' (Union x1 x2) = do
                (r1, r1') <- eval' x1
                (r2, r2') <- eval' x2
                return $ (r1 <> r2, r1' <> r2')
            eval' (Intersection x1 x2) = do
                (r1, r1') <- eval' x1
                (r2, r2') <- eval' x2
                return $ (r1 `Set.intersection` r2, r1' `Set.intersection` r2')
            eval' (LeftUnion x1 x2) = do
                (r1, r1') <- eval' x1
                (r2, r2') <- eval' x2
                return $ (r1 <> (Set.filter (not . (`Set.member` (Set.map fst r1)). fst) r2), r1' <> (Set.filter (not . (`Set.member` (Set.map snd r1')). snd) r2'))
            eval' (Difference x1 x2) = do
                (r1, r1') <- eval' x1
                (r2, r2') <- eval' x2
                return $ (r1 Set.\\ r2, r1' Set.\\ r2')
            eval' (Reverse x) = do
                (r, r') <- eval' x
                return (r', r)
            eval' (ITE xb x1 x2) = do
                (b, _) <- eval' xb
                if Set.null b then
                    eval' x2
                else
                    eval' x1
            eval' (RandomEnsureFunction False x) = do
                (r, _) <- eval' x
                f <- fmap (Set.fromAscList . Map.assocs) $ traverse pickUniformly $ Map.mapKeysWith (<>) fst $ Map.fromSet ((:[]) . snd) r
                return (f, Set.map (\(x,y) -> (y,x)) f)
            eval' (RandomEnsureFunction True x) = do
                (r, r') <- eval' x
                runIndependent ((Set.fromAscList . Map.assocs) <$> randomMaximumCardinalityMatching r') ((Set.fromAscList . Map.assocs) <$> randomMaximumCardinalityMatching r)

--based n Stefan Klinger's maxBipartiteMatching code, but with added randomness
randomMaximumCardinalityMatching :: (Ord a, Ord b, RandomGen g, MonadState g m) => Set (a,b) -> m (Map b a)
randomMaximumCardinalityMatching a = optR (Map.keys fwd, []) fwd Map.empty where
                fwd = foldr (\(x,y) -> Map.insertWith (<>) x [y]) Map.empty $ Set.toList a
                optR :: (Ord a, Ord b, RandomGen g, MonadState g m) => ([a], [a]) -> Map a [b] -> Map b a -> m (Map b a)
                optR ([],_) fwd mat = return mat
                optR (free, failed) fwd mat = do
                    (x, free') <- popUniformly free
                    r <- rightR fwd mat [] x
                    case r of
                        Left fwd' -> optR (free', x:failed) fwd' mat
                        Right mat' -> optR (free'++failed,[]) fwd mat'
                rightR rem mat path x = case Map.lookup x rem of
                    Nothing -> return $ Left rem
                    Just ys -> leftR (Map.delete x rem) mat path ys x
                leftR rem _ _ [] _ = return $ Left rem
                leftR rem mat path candidates x = do
                    (y, ys) <- popUniformly candidates
                    case Map.lookup y mat of
                        Nothing -> return $ Right $ foldr (\(v,k) -> Map.insert k v) mat ((x,y):path)
                        Just x' -> do
                            e <- rightR rem mat ((x,y):path) x'
                            case e of
                                Right mat' -> return $ Right mat'
                                Left rem' -> leftR rem' mat path ys x

popUniformly :: (RandomGen g, MonadState g m) => [a] -> m (a,[a])
popUniformly l = do
        i <- state (randomR (0,length l - 1))
        return $ (l !! i, take i l <> drop (i+1) l)
pickUniformly :: (RandomGen g, MonadState g m) => [a] -> m a
pickUniformly l = fmap fst $ popUniformly l
                -- RandomEnsureFunction :: Bool -> TypedValue a b -> TypedValue a b
                -- RandomSymmetric :: Bool -> TypedValue a b -> TypedValue a b

runIndependent :: (MonadState g m, RandomGen g) => m a -> m b -> m (a,b)
runIndependent m m' = do
        g <- state split
        a <- m
        put g
        b <- m'
        return (a,b)
