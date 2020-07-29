{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

import Data.TMCR.Logic

import Control.Arrow
import Control.Monad
import Data.Maybe
import Text.Read

import Control.Monad.State

import Control.Monad.Free

import Data.Functor.Foldable

import System.Random

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import Miso
import Miso.Html.Element
import Miso.String
-- import qualified Language.Javascript.JSaddle.Warp as JSaddle

import Control.Lens hiding (view)
import Control.Lens.TH

staticRoot :: String
staticRoot = "https://ibot02.github.io/tmcr-newstyle-logic-demo/static/"

data Action = NoOp
            | AdvanceRNG
            | SetRNG String
            | EditSyntaxTree (Free PreTypecheckValueF ())
            | RoomAddAction RoomAddAction
            | RemoveRoom String
            | RemoveDoor String
            | RemoveWarp String
            | FlagAddAction FlagAddAction
            | DropdownConfigAction DropdownConfigAction
            | RemoveFlag String
            | SetChecked String Bool
            | SetDropdownSelected String String
            -- ...
deriving instance Eq Action
deriving instance Ord Action
-- deriving instance Show Action

data RoomAddAction = AddRoom
                   | AddDoorOrWarp
                   | SetCurrentlyInputRoomName String
                   | SetCurrentlySelectedRoom1 String
                   | SetCurrentlySelectedRoom2 String
                   | SetCurrentlyInputDoor1Name String
                   | SetCurrentlyInputDoor2Name String
                   | SetCurrentlyInputIsDoor Bool
                   deriving (Eq, Ord, Show)

data FlagAddAction = AddFlag
                   | SetFlagName String
                   deriving (Eq, Ord, Show)

data DropdownConfigAction = AddDropdown
                          | SetDropdownName String
                          | SetDropdownOptions String [String]
                          | RemoveDropdown String
                          deriving (Eq, Ord, Show)

data Model = Model {
          _modelAST :: Free PreTypecheckValueF ()
        , _modelRooms :: Set String
        , _modelDoors :: Set DoorData
        , _modelOneWayWarps :: Set WarpData
        , _modelFlagSet :: Set String
        , _modelCurrentFlagNameInput :: String
        , _modelDropdownOptions :: Map String [String]
        , _modelCurrentDropdownNameInput :: String
        , _modelActiveFlags :: Set String
        , _modelCurrentDropdownSelections :: Map String String
        , _modelRoomDataDialog :: RoomDataDialogModel
        , _modelRNG :: Int
        } 

deriving instance Eq Model
deriving instance Ord Model
-- deriving instance Show Model

data RoomDataDialogModel = RoomDataDialogModel {
          _roomDialogModelNewRoom :: String
        , _roomDialogModelRoom1 :: String
        , _roomDialogModelRoom2 :: String
        , _roomDialogModelDoor1 :: String
        , _roomDialogModelDoor2 :: String
        , _roomDialogModelIsDoor :: Bool
        } deriving (Eq, Ord, Show)

$(makeLenses ''Model)
$(makeLenses ''RoomDataDialogModel)

main = do
    m <- initialModel
    startApp App {
          initialAction = NoOp
        , model = m
        , update = updateModel
        , view = viewModel
        , events = defaultEvents
        , subs = []
        , mountPoint = Nothing
        , logLevel = Off
        }

initialModel :: IO Model
initialModel = do
    g <- getStdGen
    return Model {
      _modelAST = return ()
    , _modelRooms = Set.empty
    , _modelDoors = Set.empty
    , _modelOneWayWarps = Set.empty
    , _modelFlagSet = Set.empty
    , _modelDropdownOptions = Map.empty
    , _modelActiveFlags = Set.empty
    , _modelCurrentDropdownSelections = Map.empty
    , _modelRoomDataDialog = RoomDataDialogModel "" "" "" "" "" True
    , _modelCurrentFlagNameInput = ""
    , _modelCurrentDropdownNameInput = ""
    , _modelRNG = fst $ random g
    }

updateModel :: Action -> Model -> Effect Action Model
updateModel (RoomAddAction AddRoom) = fromTransition $ do
                newRoomName <- use $ modelRoomDataDialog . roomDialogModelNewRoom
                modelRooms <>= Set.singleton newRoomName
updateModel (RoomAddAction AddDoorOrWarp) = fromTransition $ do
                room1Name <- use $ modelRoomDataDialog . roomDialogModelRoom1
                room2Name <- use $ modelRoomDataDialog . roomDialogModelRoom2
                warp1Name <- use $ modelRoomDataDialog . roomDialogModelDoor1
                warp2Name <- use $ modelRoomDataDialog . roomDialogModelDoor2
                isDoor <- use $ modelRoomDataDialog . roomDialogModelIsDoor
                if isDoor
                then do
                    warps <- use $ modelDoors . folded . to (doorName1 &&& doorName2) . each . to Set.singleton
                    unless (warp1Name `elem` warps || warp2Name `elem` warps) $ modelDoors <>= Set.singleton (DoorData warp1Name warp2Name room1Name room2Name)
                else do
                    warps <- use $ modelOneWayWarps . folded . to warpName . to Set.singleton
                    unless (warp1Name `elem` warps) $ modelOneWayWarps <>= Set.singleton (WarpData warp1Name room1Name room2Name)
updateModel (RoomAddAction a) = fromTransition $ case a of
                SetCurrentlyInputRoomName s -> modelRoomDataDialog . roomDialogModelNewRoom .= s
                SetCurrentlySelectedRoom1 s -> modelRoomDataDialog . roomDialogModelRoom1 .= s
                SetCurrentlySelectedRoom2 s -> modelRoomDataDialog . roomDialogModelRoom2 .= s
                SetCurrentlyInputDoor1Name s -> modelRoomDataDialog . roomDialogModelDoor1 .= s
                SetCurrentlyInputDoor2Name s -> modelRoomDataDialog . roomDialogModelDoor2 .= s
                SetCurrentlyInputIsDoor s -> modelRoomDataDialog . roomDialogModelIsDoor .= s
updateModel (FlagAddAction a) = fromTransition $ case a of
                AddFlag -> do
                    name <- use modelCurrentFlagNameInput
                    modelFlagSet <>= Set.singleton name
                SetFlagName s -> modelCurrentFlagNameInput .= s
updateModel (DropdownConfigAction a) = fromTransition $ case a of
                AddDropdown -> do
                    name <- use modelCurrentDropdownNameInput
                    modelDropdownOptions <>= Map.singleton name []
                SetDropdownName s -> modelCurrentDropdownNameInput .= s
                RemoveDropdown s -> do
                    modelDropdownOptions %= Map.delete s
                    modelCurrentDropdownSelections %= Map.delete s
                SetDropdownOptions s o -> do
                    modelDropdownOptions %= Map.insert s o
                    modelCurrentDropdownSelections . Control.Lens.at s . _Just %= (\o' -> if o' `elem` o then o' else "")
updateModel (RemoveRoom r) = fromTransition $ do
                    modelRooms %= Set.delete r
                    modelOneWayWarps %= Set.filter (\w -> warpSourceRoom w /= r && warpTargetRoom w /= r)
                    modelDoors %= Set.filter (\d -> doorRoom1 d /= r && doorRoom2 d /= r)
updateModel (RemoveDoor d) = fromTransition $ modelDoors %= Set.filter (\d' -> doorName1 d' /= d && doorName2 d' /= d)
updateModel (RemoveWarp w) = fromTransition $ modelOneWayWarps %= Set.filter ((/= w) . warpName)
updateModel (RemoveFlag s) = fromTransition $ do
                    modelFlagSet %= Set.delete s
                    modelActiveFlags %= Set.delete s
updateModel (SetChecked s b) = fromTransition $ if b
                    then modelActiveFlags %= Set.insert s
                    else modelActiveFlags %= Set.delete s
updateModel (SetDropdownSelected s o) = fromTransition $ 
                    modelCurrentDropdownSelections %= Map.insert s o
updateModel (EditSyntaxTree newAST) = fromTransition $ modelAST .= newAST
updateModel AdvanceRNG = fromTransition $ modelRNG %= fst . random . mkStdGen
updateModel (SetRNG s) = fromTransition $ case readMaybe s of
                Nothing -> return ()
                Just i -> modelRNG .= i
updateModel NoOp = fromTransition $ return ()

viewModel :: Model -> View Action
viewModel model = div_ [] [
              roomDataDialog model
            , optionConfiguration model
            , astEditor model
            , div_ [] [optionSelection model, rngSet model]
            , outputArea model
            , link_ [ rel_ "stylesheet"
                    , href_ (toMisoString $ staticRoot ++ "style.css")
                    ]
            ]

roomDataDialog :: Model -> View Action
roomDataDialog model = div_ [class_ "room-data-dialog"] [
              roomList model
            , doorList model
            , oneWayWarpList model
            , newRoom model
            , newWarp model
            ]

roomList :: Model -> View Action
roomList model = div_ [] $ fmap roomView $ Set.toList $ _modelRooms model

roomView :: String -> View Action
roomView name = span_ [] [
              button_ [onClick (RemoveRoom name), name_ "remove"] [text "\x1F5D1"]
            , text $ toMisoString name
            ]

doorList :: Model -> View Action
doorList model = div_ [] $ fmap viewDoorData (model ^.. modelDoors . folded) where
            viewDoorData d = span_ [] [
                  button_ [onClick (RemoveDoor (doorName1 d)), name_ "remove"] [text "\x1F5D1"]
                , span_ [class_ "room-name"] [text $ toMisoString $ doorRoom1 d]
                , text "."
                , span_ [class_ "door-name"] [text $ toMisoString $ doorName1 d]
                , text " connects to "
                , span_ [class_ "room-name"] [text $ toMisoString $ doorRoom2 d]
                , text "."
                , span_ [class_ "door-name"] [text $ toMisoString $ doorName2 d]
                ]

oneWayWarpList :: Model -> View Action
oneWayWarpList model = div_ [] $ fmap viewWarpData (model ^.. modelOneWayWarps . folded) where
            viewWarpData w = span_ [] [
                  button_ [onClick (RemoveWarp (warpName w)), name_ "remove"] [text "\x1F5D1"]
                , span_ [class_ "room-name"] [text $ toMisoString $ warpSourceRoom w]
                , text "."
                , span_ [class_ "warp-name"] [text $ toMisoString $ warpName w]
                , text " goes to "
                , span_ [class_ "room-name"] [text $ toMisoString $ warpTargetRoom w]
                ]

newRoom :: Model -> View Action
newRoom model = div_ [] [text "Add Room", form_ [onSubmit (RoomAddAction AddRoom)] [input_ [required_ True, onChange (RoomAddAction . SetCurrentlyInputRoomName . fromMisoString)], input_ [type_ "submit"]]]
newWarp :: Model -> View Action
newWarp model = div_ [] [ text "Add Warp" , form_ [onSubmit (RoomAddAction AddDoorOrWarp)] [
                  input_ [required_ True, onChange (RoomAddAction . SetCurrentlyInputDoor1Name . fromMisoString)]
                , span_ [] [
                      input_ [id_ "roomDialogIsDoorCheckbox", type_ "checkbox", checked_ (model ^. modelRoomDataDialog . roomDialogModelIsDoor), onChecked (\(Checked b) -> RoomAddAction $ SetCurrentlyInputIsDoor b)]
                    , label_ [for_ "roomDialogIsDoorCheckbox"] [text "Two-Way"]
                    ]
                , input_ ((let b = model ^. modelRoomDataDialog . roomDialogModelIsDoor in [required_ b, disabled_ (not b)]) ++ [onChange (RoomAddAction . SetCurrentlyInputDoor2Name . fromMisoString)])
                , select_ [required_ True, onChange (RoomAddAction . SetCurrentlySelectedRoom1 . fromMisoString)] $
                    option_ [] []:fmap (\roomName -> option_ [] [text $ toMisoString roomName]) (model ^.. modelRooms . folded)
                    
                , select_ [required_ True, onChange (RoomAddAction . SetCurrentlySelectedRoom2 . fromMisoString)] $
                    option_ [] []:fmap (\roomName -> option_ [] [text $ toMisoString roomName]) (model ^.. modelRooms . folded)
                , input_ [type_ "submit"]
                ]]

optionConfiguration :: Model -> View Action
optionConfiguration model = div_ [class_ "option-config"] [
              div_ [class_ "flag-config"] $ text "Flags:" : span_ [] [
                form_ [onSubmit (FlagAddAction AddFlag)] [
                      input_ [onChange (FlagAddAction . SetFlagName . fromMisoString)]
                    , input_ [type_ "submit", value_ "+"]
                ]] : fmap (\flagName -> span_ [] [button_ [name_ "Remove", onClick (RemoveFlag flagName)] [text "-"], text (toMisoString flagName)]) (model ^.. modelFlagSet . folded)
            , div_ [class_ "dropdown-config"] $ text "Dropdowns:" : span_ [] [
                form_ [onSubmit (DropdownConfigAction AddDropdown)] [
                      input_ [onChange (DropdownConfigAction . SetDropdownName . fromMisoString)]
                    , input_ [type_ "submit", value_ "+"]
                ]] : fmap (\dropdownName -> span_ [] [button_ [name_ "Remove", onClick (DropdownConfigAction $ RemoveDropdown dropdownName)] [text "-"], text (toMisoString dropdownName), textarea_ [onChange (DropdownConfigAction . SetDropdownOptions dropdownName . Prelude.lines . fromMisoString)] []]) (model ^.. modelDropdownOptions . to Map.keysSet . folded)
            ]

astEditor :: Model -> View Action
astEditor model = snd (iter helper model') id where
            model' = fmap (\() -> (pure () :: Free PreTypecheckValueF (), \context -> div_ [class_ "ast"] [selection context (pure ()) options])) $ model ^. modelAST
            selection :: (a -> Free PreTypecheckValueF ()) -> a -> [(String, View Action, a)] -> View Action
            selection context defaultOption options = select_ [onChange (setChoice context defaultOption options . fromMisoString)] (options ^.. folded . _2)
            setChoice context defaultOption options value = EditSyntaxTree $ context $ fromMaybe defaultOption $ options ^? folded . filtered ((== value) . (^. _1)) . _3
            options :: [(String, View Action, Free PreTypecheckValueF ())]
            options = 
                  ("Blank", option_ [value_ "Blank"] [], pure ()):
                fmap (\(n, v) -> (n, option_[] [text (toMisoString n)], wrap (fmap pure v))) [
                  ("Vanilla", PTCVanillaF)
                , ("Door to Warp", PTCDoorWarpF)
                , ("Door to Target", PTCDoorTargetF)
                , ("Constant Warp(s)", PTCConstantWarpF Data.TMCR.Logic.All)
                , ("Constant Target(s)", PTCConstantTargetF Data.TMCR.Logic.All)
                , ("Constant Door(s)", PTCConstantDoorF Data.TMCR.Logic.All)
                , ("Constant Atom(s)", PTCAtomSetF Set.empty)
                , ("Flag", PTCGivenFlagF "")
                , ("Dropdown", PTCGivenDropdownF "")
                , ("Composition", PTCComposeF () ())
                , ("Union", PTCUnionF () ())
                , ("Intersection", PTCIntersectionF () ())
                , ("Difference", PTCDifferenceF () ())
                , ("Left Union", PTCLeftUnionF () ())
                , ("Identity", PTCIdentityF)
                , ("Empty", PTCEmptyF)
                , ("Reverse", PTCReverseF ())
                , ("If-Then-Else", PTCITEF () () ())
                , ("Restrict to Function", PTCRandomEnsureFunctionF False ())
                , ("Restrict to Injection", PTCRandomEnsureFunctionF True ())
                ] ++ [("Make Symmetric Function", option_ [disabled_ True] [text "Make Symmetric Function"], pure ())]
            helper :: PreTypecheckValueF (Free PreTypecheckValueF (), (Free PreTypecheckValueF () -> Free PreTypecheckValueF ()) -> View Action) -> (Free PreTypecheckValueF (), (Free PreTypecheckValueF () -> Free PreTypecheckValueF ()) -> View Action)
            helper f = (wrap (fmap fst f), \context -> div_ [class_ "ast"] (selection context (pure ()) options : helper' f context))
            constantSelection tags names context = selection context Data.TMCR.Logic.All $ ("All", option_ [] [text "All"], Data.TMCR.Logic.All) : fmap (\t -> ("Tagged " ++ t, option_ [] [text $ toMisoString ("Tagged" ++ t)], Tagged t)) tags ++ fmap (\n -> ("Named " ++ n, option_ [] [text $ toMisoString ("Named \"" ++ n ++ "\"")], Named n)) names
            pairHelper c (v1, x1) (v2, x2) context = [div_ [class_ "ast-pair"] [
                          x1 (\v -> context $ wrap $ c v v2)
                        , x2 (\v -> context $ wrap $ c v1 v)
                        ]]
            helper' PTCVanillaF _ = []
            helper' PTCDoorWarpF _ = []
            helper' PTCDoorTargetF _ = []
            helper' (PTCConstantWarpF _) context = [constantSelection [] (model ^.. modelOneWayWarps . folded . to warpName) (context . wrap . PTCConstantWarpF)]
            helper' (PTCConstantTargetF _) context = [constantSelection [] (model ^.. modelOneWayWarps . folded . to warpName) (context . wrap . PTCConstantTargetF)]
            helper' (PTCConstantDoorF _) context = [constantSelection [] (model ^.. modelDoors . folded . to (doorName1 &&& doorName2) . each) (context . wrap . PTCConstantDoorF)]
            helper' (PTCGivenFlagF _) context = [selection (context . wrap . PTCGivenFlagF) "" $ ("", option_ [] [], "") : (fmap (\s -> (s, option_ [] [text $ toMisoString s], s)) $ model ^.. modelFlagSet . folded)]
            helper' (PTCGivenDropdownF _) context = [selection (context . wrap . PTCGivenDropdownF) "" $ ("", option_ [] [], "") : (fmap (\s -> (s, option_ [] [text $ toMisoString s], s)) $ model ^.. modelDropdownOptions . to Map.keysSet . folded)]
            helper' (PTCAtomSetF _) context = [textarea_ [class_ "ast-atom-set", onChange (EditSyntaxTree . context . wrap . PTCAtomSetF . Set.fromList . Prelude.lines . fromMisoString)] []]
            helper' PTCIdentityF _ = []
            helper' PTCEmptyF _ = []
            helper' (PTCComposeF x1 x2) context = pairHelper PTCComposeF x1 x2 context
            helper' (PTCUnionF x1 x2) context = pairHelper PTCUnionF x1 x2 context
            helper' (PTCIntersectionF x1 x2) context = pairHelper PTCIntersectionF x1 x2 context
            helper' (PTCDifferenceF x1 x2) context = pairHelper PTCDifferenceF x1 x2 context
            helper' (PTCLeftUnionF x1 x2) context = pairHelper PTCLeftUnionF x1 x2 context
            helper' (PTCReverseF (_,x)) context = [x $ context . wrap . PTCReverseF]
            helper' (PTCITEF (v1, x1) (v2, x2) (v3, x3)) context = [div_ [class_ "ast-if-then-else"] [
                                           div_ [] [text "If", x1 (\v -> context $ wrap $ PTCITEF v v2 v3)]
                                         , div_ [] [text "Then", x2 (\v -> context $ wrap $ PTCITEF v1 v v3)]
                                         , div_ [] [text "Else", x3 (\v -> context $ wrap $ PTCITEF v1 v2 v)]
                                         ]]
            helper' (PTCRandomEnsureFunctionF b (_,x)) context = [x $ context . wrap . PTCRandomEnsureFunctionF b]
            helper' _ _ = [text "TODO"]

optionSelection :: Model -> View Action
optionSelection model = div_ [class_ "option-select"] $ flagSelection model ++ dropdownSelection model where
    flagSelection model = fmap (\name -> span_ [] [input_ [type_ "checkbox", onChecked (\(Checked b) -> SetChecked name b)], text (toMisoString name)]) $ model ^.. modelFlagSet . folded
    dropdownSelection model = fmap (\(name, options) -> span_ [] [text (toMisoString name), select_ [onChange (SetDropdownSelected name . fromMisoString)] (option_ [] [] : fmap (option_ [] . (:[]) . text . toMisoString) options)] ) $ model ^. modelDropdownOptions . to Map.assocs

rngSet :: Model -> View Action
rngSet model = span_ [] [label_ [for_ "rng"] [text "RNG: "], input_ [id_ "rng", value_ (toMisoString $ show $ model ^. modelRNG), onChange (SetRNG . fromMisoString)], button_ [onClick AdvanceRNG] ["Step RNG"]]

makeAST :: (Traversable f, Base t ~ f, Corecursive t) => Free f a -> Either a t
makeAST (Pure v) = Left v
makeAST (Free f) = fmap embed $ traverse makeAST f

outputArea :: Model -> View Action
outputArea model = div_ [] $ case makeAST (model ^. modelAST) of
        Left () -> [text "The AST is incomplete"]
        Right ast -> case typecheck ast of
            Left _ -> [text "The AST has type errors"]
            Right typed -> let doorData = model ^. modelDoors
                               warpData = model ^. modelOneWayWarps
                               flagData = model ^. modelActiveFlags . to (Map.fromSet (const True))
                               dropdownData = model ^. modelCurrentDropdownSelections
                               extraData = ExtraData doorData warpData flagData dropdownData
                               result = evalState (eval extraData typed) (model ^. modelRNG . to mkStdGen)
                           in fmap (\(WarpRep s, WarpTargetRep s') -> span_ [] [text (toMisoString (show s)), text " goes to ", text (toMisoString (show s'))]) $ Set.toList result
