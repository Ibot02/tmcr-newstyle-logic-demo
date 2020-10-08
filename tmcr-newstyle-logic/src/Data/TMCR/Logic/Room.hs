{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
module Data.TMCR.Logic.Room where

import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer

import Control.Monad.Reader

import Data.Char (isSeparator)

import Data.Void

data LogicRoom = LogicRoom
                deriving (Eq, Ord, Show)

data Typedef = TypedefNamed String
             | TypedefScoping String
             | TypedefAnon String
             | TypedefOp String
             deriving (Eq, Ord, Show)

data Sugar = SugarOpList String String
         deriving (Eq, Ord, Show)

data Value = Anon String
           | NamedScoped String ScopedName
           | NamedScoping String String
           | Op ScopedName String ScopedName
           deriving (Eq, Ord, Show)

data ScopedName = Global String
                | Scoped [String]
                deriving (Eq, Ord, Show)

data Mode = ModeDefault --select or new
          | ModeAppend
          | ModeReplace
          deriving (Eq, Ord, Show)

type Forest = [Tree]
data Tree = Node Value Mode Forest
            deriving (Eq, Ord, Show)

nonLinebreakSpace :: Char -> Bool
nonLinebreakSpace c = isSeparator c && not (c `elem` "\n\r")

sc :: (MonadParsec e s m, Token s ~ Char) => m ()
sc = Text.Megaparsec.Char.Lexer.space (void $ takeWhile1P (Just "space") nonLinebreakSpace) empty empty

logicParser :: ReaderT ([Typedef], [Sugar]) (Parsec Void String) Forest
logicParser = parseForest "" where
    parseForest :: String -> ReaderT ([Typedef], [Sugar]) (Parsec Void String) Forest
    parseForest indent = many (eol @ Void @ String) *> some (parseTree indent <* many eol)
    parseTree :: String -> ReaderT ([Typedef], [Sugar]) (Parsec Void String) Tree
    parseTree indent = try (consumeIndent indent) *> ((parseSugarOpList <* eol) <|> (do
        v <- parseValue
        (m,c) <- (do
            m <- parseMode
            c <- label "Children" $ try (inlineChildren <* eol) <|> (eol *> multilineChildren indent)
            return (m, c)
            ) <|> ((ModeDefault, []) <$ eol)
        return $ Node v m c
        ))
    parseValue :: ReaderT ([Typedef], [Sugar]) (Parsec Void String) Value
    parseValue = asks fst >>= choice . fmap (\case
        TypedefNamed t -> try $ do
            t' <- symbol sc t
            (NamedScoped t' <$> parseScopedName)
        TypedefAnon t -> try $ Anon <$> symbol sc t
        TypedefOp t -> try $ Op <$> parseScopedName <*> symbol sc t <*> parseScopedName
        TypedefScoping t -> try $ do
            t' <- symbol sc t
            NamedScoping t' <$> lexeme sc parseName
        )
    parseScopedName :: ReaderT ([Typedef], [Sugar]) (Parsec Void String) ScopedName
    parseScopedName = lexeme sc $ (char 'g' *> (Global <$> parseName)) <|> (Scoped <$> parseName `sepBy` (char '.'))
    parseName :: ReaderT ([Typedef], [Sugar]) (Parsec Void String) String
    parseName = between (char '"') (char '"') (many possiblyEscapedChar) <|> many alphaNumChar
    possiblyEscapedChar :: ReaderT ([Typedef], [Sugar]) (Parsec Void String) Char
    possiblyEscapedChar = do
        c <- satisfy (/= '"')
        case c of
            '\\' -> anySingle
            _ -> return c
    parseMode :: ReaderT ([Typedef], [Sugar]) (Parsec Void String) Mode
    parseMode = lexeme sc $ label "mode" $ (ModeDefault <$ char ':') <|> (ModeAppend <$ string "+:") <|> (ModeReplace <$ string "!:")
    inlineChildren :: ReaderT ([Typedef], [Sugar]) (Parsec Void String) Forest
    inlineChildren = label "inlined Childen" $ inlineChild `sepBy1` (symbol sc ",")
    inlineChild :: ReaderT ([Typedef], [Sugar]) (Parsec Void String) Tree
    inlineChild = between (symbol sc "(") (symbol sc ")") inlineChild <|> (do
        v <- parseValue
        (m,c) <- option (ModeDefault, []) $ do
            m <- parseMode
            c <- inlineChildren
            return (m,c)
        return $ Node v m c
        )
    multilineChildren :: String -> ReaderT ([Typedef], [Sugar]) (Parsec Void String) Forest
    multilineChildren indent = do
        indent' <- findIndent indent
        parseForest indent'
    findIndent :: String -> ReaderT ([Typedef], [Sugar]) (Parsec Void String) String
    findIndent indent = try $ lookAhead $ do
        consumeIndent indent
        indent' <- takeWhile1P (Just "indentation") nonLinebreakSpace
        satisfy (not . isSeparator)
        return $ indent ++ indent'
    consumeIndent :: String -> ReaderT ([Typedef], [Sugar]) (Parsec Void String) String
    consumeIndent indent = string indent <?> "indentation"
    parseSugarOpList :: ReaderT ([Typedef], [Sugar]) (Parsec Void String) Tree
    parseSugarOpList = asks snd >>= choice . fmap (\(SugarOpList name sep) -> try $
        between (symbol sc "(") (symbol sc ")") $ Node (Anon name) ModeDefault <$> inlineChild `sepBy` (symbol sc sep))





