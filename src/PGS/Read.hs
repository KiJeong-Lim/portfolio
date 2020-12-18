module PGS.Read where

import Control.Applicative
import Control.Monad
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Text.PC
import Lib.Text.PC.Expansion
import PGS.Util

acceptList :: PC a -> PC [a]
acceptList pc = consumePC "[" *> (skipWhite *> (pure [] <|> (pure (:) <*> pc <*> many (consumePC "," *> skipWhite *> pc)))) <* consumePC "]"

readTSym :: PC TSym
readTSym = mconcat
    [ consumePC "\\$" *> pure TSEOF
    , consumePC "$" *> (TSVar <$> smallid)
    ]

readNSym :: PC NSym
readNSym = go 0 where
    go :: Int -> PC NSym
    go 0 = List.foldl' NSApp <$> go 1 <*> many (consumePC " " *> go 1)
    go 1 = mconcat
        [ consumePC "$" *> (NSVar <$> largeid)
        , go 2
        ]
    go _ = consumePC "(" *> go 0 <* consumePC ")"

readDestructors :: PC [Destructor]
readDestructors
    = mconcat
        [ do
            de <- DsSource <$> regexPC "[.\\'\\n'\\'$'\\'\\\"']+"
            des <- readDestructors
            return (de : des)
        , do
            de <- DsStrLit <$> acceptQuote
            des <- readDestructors
            return (de : des)
        , do
            consumePC "$"
            negPC (acceptPC (\ch -> ch == ' '))
            idx <- readInt
            de <- mconcat
                [ do
                    consumePC "."
                    field <- regexPC "['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*"
                    return (DsTSPatn idx field)
                , negPC (consumePC ".") *> pure (DsNSPatn idx)
                ]
            des <- readDestructors
            return (de : des)
        , do
            consumePC "$"
            str <- many (acceptPC (\ch -> ch == ' '))
            if str == "" then negPC readInt else return ()
            des <- readDestructors
            return (DsSource ("$" ++ str) : des)
        , lend *> pure []
        ]
    where
        readInt :: PC Int
        readInt = autoPC "int"

readSym :: PC Sym
readSym = mconcat
    [ NS <$> readNSym
    , TS <$> readTSym
    ]

readYMatch :: PC YMatch
readYMatch = do
    indent 4
    prec <- autoPC "int"
    skipWhite
    pats <- acceptList readSym
    consumePC ":"
    lend
    dess <- many (indent 8 *> readDestructors)
    return $ YMatch
        { getMatchingPrec = prec
        , getMatchingPats = pats
        , getDestructorss = dess
        }

readScheme :: PC Scheme
readScheme = do
    consumePC "\\define"
    type_constraint <- mconcat
        [ do
            type_ctx <- acceptQuote
            skipWhite
            consumePC "=>"
            return (Just type_ctx)
        , pure Nothing
        ]
    skipWhite
    consumePC "$"
    body_name <- largeid
    params_decl <- many $ do
        skipWhite
        consumePC "("
        consumePC "$"
        param_name <- largeid
        skipWhite
        consumePC ":"
        skipWhite
        param_type <- acceptQuote
        consumePC ")"
        return (param_name, param_type)
    skipWhite
    consumePC ":"
    skipWhite
    body_type <- acceptQuote
    skipWhite
    consumePC "{"
    lend
    matches <- many readYMatch
    consumePC "}"
    lend
    return $ Scheme
        { getTypeConstr = type_constraint
        , getSchemeDecl = (body_name, body_type)
        , getParamsDecl = params_decl
        , getMatchDecls = matches
        }

readAssoc :: PC Associativity
readAssoc = mconcat
    [ consumePC "none" *> pure ANone
    , consumePC "left" *> pure ALeft
    , consumePC "right" *> pure ARight
    ]

readTerminalInfo :: PC TerminalInfo
readTerminalInfo = do
    indent 8
    patn <- acceptQuote
    consumePC ":"
    skipWhite
    name <- readTSym
    skipWhite
    prec <- autoPC "int"
    skipWhite
    assoc <- readAssoc
    lend
    return $ TerminalInfo
        { getTerminalPatn = patn
        , getTerminalName = name
        , getTerminalPrec = prec
        , getTerminalAsso = assoc
        }

readTarget :: PC YTarget
readTarget = do
    consumePC "\\target"
    skipWhite
    consumePC "{"
    lend
    indent 4
    consumePC "token-type:"
    skipWhite
    token_type <- acceptQuote
    lend
    indent 4
    consumePC "parser-name:"
    skipWhite
    parser_name <- acceptQuote
    lend
    indent 4
    consumePC "result-type:"
    skipWhite
    result_type <- acceptQuote
    lend
    indent 4
    consumePC "start:"
    skipWhite
    start <- readNSym
    lend
    indent 4
    consumePC "terminals:"
    lend
    terminal_infos <- many readTerminalInfo
    consumePC "}"
    lend
    return $ YTarget
        { getTokenType = token_type
        , getParserName = parser_name
        , getResultType = result_type
        , getStartSymbol = start
        , getTerminalInfos = terminal_infos
        }

readBlock :: PC YBlock
readBlock = mconcat
    [ do
        consumePC "\\hshead"
        skipWhite
        consumePC "{"
        lend
        hshead <-  many ((indent 4 *> regexPC "[.\\'\\n']*" <* lend) <|> (lend *> pure ""))
        consumePC "}"
        lend
        return (HsHead hshead)
    , do
        consumePC "\\hstail"
        skipWhite
        consumePC "{"
        lend
        hstail <- many ((indent 4 *> regexPC "[.\\'\\n']*" <* lend) <|> (lend *> pure ""))
        consumePC "}"
        lend
        return (HsTail hstail)
    , Define <$> readScheme
    , Target <$> readTarget
    ]
